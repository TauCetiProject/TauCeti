/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Coxeter.Element.Conj
public import TauCeti.LinearAlgebra.RootSystem.Coxeter.Element.Orbit
public import TauCeti.RepresentationTheory.SymmetricAlgebra.Weyl.CoprimeExponents
public import TauCeti.RepresentationTheory.SymmetricAlgebra.Weyl.Coxeter.Element
public import TauCeti.RingTheory.Polynomial.Cyclotomic.Exponents
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.RootSystem.BaseExists
import Mathlib.RingTheory.RootsOfUnity.Complex
import TauCeti.LinearAlgebra.RootSystem.Basic
import TauCeti.LinearAlgebra.RootSystem.Coxeter.Element.ActsBy
import TauCeti.LinearAlgebra.RootSystem.Coxeter.Element.BaseChange
import TauCeti.LinearAlgebra.RootSystem.Coxeter.Element.Plane
import TauCeti.LinearAlgebra.RootSystem.Coxeter.FixedPoints
import TauCeti.RepresentationTheory.SymmetricAlgebra.Weyl.BaseChange

/-!
# The exponents of a Weyl group

Let `b` be a base of a finite irreducible reduced crystallographic root system of rank `r`. Let
`c` be a Coxeter element, a product of the `r` simple reflections in some order, and let `h` be
its order, the **Coxeter number**. The root-count identity `|Φ| = r h` already lives in
`TauCeti.LinearAlgebra.RootSystem.Coxeter.Number`
(`RootPairing.Base.natCard_eq_card_support_mul_orderOf_wordProd`); this file focuses on the
degrees `dᵢ` and exponents `eᵢ = dᵢ - 1` of a homogeneous basic invariant system of `Sym(M*)^W`.

Over an algebraically closed field `K` containing `ℝ` (such as `ℂ`), this file first proves
`RootPairing.degree_sub_one_lt_orderOf_wordProd`: every exponent `dᵢ - 1` is less than `h`
(deriving `|Φ| = r h` internally along the way). It then extends the exponent theorems to
arbitrary characteristic-zero fields `K` via base change from the rational model `b.rationalModel`
to `ℂ` (`TauCeti.LinearAlgebra.RootSystem.Coxeter.Element.BaseChange` and
`TauCeti.RepresentationTheory.SymmetricAlgebra.Weyl.BaseChange`), together with the regular
eigenvector for `exp (-2πi / h)` from the Coxeter plane construction
(`TauCeti.LinearAlgebra.RootSystem.Coxeter.Element.Plane`) and cyclotomic descent
(`TauCeti.RepresentationTheory.SymmetricAlgebra.Weyl.CoprimeExponents` and
`TauCeti.RingTheory.Polynomial.Cyclotomic.Exponents`):

* Degree bounds `2 ≤ dᵢ ≤ h`.
* Exponent duality `dᵢ - 1 ↦ h - (dᵢ - 1)`.
* The crystallographic coprime-exponent theorem (including `2` and `h`).
* `(P.weylGroupRootRep c).charpoly = ∏ i, (X - C (ζ ^ (dᵢ - 1)))` for any primitive `h`-th
  root of unity `ζ : K`.

## The argument

Over `ℂ`, the bipartite Coxeter element `c` has a regular eigenvector for a primitive `h`-th root
of unity `ζ`, and since its characteristic polynomial is rational, the eigenvalue computation there
holds with `ζ` replaced by any primitive `h`-th root of unity
(`RootPairing.charpoly_weylGroupRootRep_of_isRegularWeight_of_isPrimitiveRoot`). Using `ζ` and
`ζ⁻¹` shows that the exponents `eᵢ` modulo `h` are stable under `e ↦ -e`, with multiplicity.
None of them is `0` modulo `h`, as `1` is not an eigenvalue of `c`, so they pair off and
`2 ∑ᵢ (eᵢ % h) = r h`. On the other hand `∑ᵢ eᵢ = |Φ⁺|`
(`RootPairing.sum_sub_one_eq_ncard_posRoots_of_bijective_aeval_weylGroupRootRep_dual`) and every
`⟨c⟩`-orbit of roots meets the inversion set of `c`, which has `r` elements, within `h` steps,
so `2 |Φ⁺| = |Φ| ≤ r h` (`TauCeti.natCard_le_orderOf_wordProd_mul_length`). As `eᵢ % h ≤ eᵢ`,
all these inequalities are equalities: `eᵢ % h = eᵢ`. Since all Coxeter elements are conjugate,
the bound holds for every Coxeter element.

Over an arbitrary characteristic-zero field `K`, the base-changed rational model
`rootPairingBaseChange ℂ b.rationalModel b.rationalModel_toLinearMap` has the same Cartan matrix
and the same graded invariant-degree multiset as `P`, so `orderOf c`, basic invariant degrees,
and the rational characteristic polynomial descend from `ℂ` to `K`.

## Main results

* `RootPairing.degree_sub_one_lt_orderOf_wordProd`: over an algebraically closed field containing
  `ℝ`, every exponent `dᵢ - 1` of a homogeneous basic invariant system is less than `h`.
* `RootPairing.two_le_and_le_orderOf_wordProd_of_bijective_aeval_weylGroupRootRep_dual`: over any
  characteristic-zero field, `2 ≤ dᵢ ≤ h`.
* `RootPairing.map_sub_one_eq_map_orderOf_sub_of_bijective_aeval_weylGroupRootRep_dual`: exponent
  duality `dᵢ - 1 ↦ h - (dᵢ - 1)`.
* `RootPairing.exists_degree_sub_one_eq_of_coprime_orderOf_wordProd`,
  `RootPairing.exists_degree_eq_two_of_bijective_aeval_weylGroupRootRep_dual`, and
  `RootPairing.exists_degree_eq_orderOf_wordProd_of_bijective_aeval_weylGroupRootRep_dual`: the
  crystallographic coprime-exponent theorem and occurrence of `2` and `h`.
* `RootPairing.charpoly_weylGroupRootRep_wordProd_eq_prod`: over any characteristic-zero field `K`
  and any primitive `h`-th root of unity `ζ : K`, `(P.weylGroupRootRep c).charpoly` equals
  `∏ i, (X - C (ζ ^ (dᵢ - 1)))`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. V, §6, no. 2.
* A. J. Coleman, *The Betti numbers of the simple Lie groups*, Canad. J. Math. **10** (1958),
  349–356.
* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, Cambridge University Press (1990),
  §§3.18–3.20.
* T. A. Springer, *Regular elements of finite reflection groups*, Invent. Math. **25** (1974),
  159–198, §4.
* R. Steinberg, *Finite reflection groups*, Trans. Amer. Math. Soc. **91** (1959), 493–504.
-/

public section

open Matrix Polynomial SymmetricAlgebra TauCeti TauCeti.SymmetricAlgebra

namespace RootPairing

variable {ι K M N κ : Type*} [Field K] [CharZero K] [Algebra ℝ K] [IsAlgClosed K]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
  (P : RootPairing ι K M N) [Finite ι] [Nonempty ι] [P.IsCrystallographic] [P.IsReduced]
  [P.IsIrreducible]

/-- Internally over `K` containing `ℝ` and algebraically closed, `|Φ| = r h` and `eᵢ < h` for
the bipartite Coxeter element. -/
private theorem natCard_eq_and_degree_sub_one_lt_orderOf_bipartiteCoxeterElement
    [FiniteDimensional K M] [Finite κ]
    (b : P.Base) (c : (coxeterMatrixOfBase P b).graph.Coloring Bool)
    {f : κ → P.weylGroupRootRep.dual.symmetricAlgebraInvariants} {d : κ → ℕ}
    (hf : ∀ k, (f k : SymmetricAlgebra K (Module.Dual K M)) ∈
      homogeneousSubmodule K (Module.Dual K M) (d k))
    (hbij : Function.Bijective (MvPolynomial.aeval (R := K) f)) :
    Nat.card ι =
        Module.finrank K M * orderOf ((weylCoxeterSystem P b).bipartiteCoxeterElement c) ∧
      ∀ k, d k - 1 < orderOf ((weylCoxeterSystem P b).bipartiteCoxeterElement c) := by
  classical
  have := Fintype.ofFinite κ
  set g := (weylCoxeterSystem P b).bipartiteCoxeterElement c
  have := P.finite_weylGroup_of_base b
  have : NeZero (orderOf g) := ⟨(orderOf_pos g).ne'⟩
  -- Springer's formula holds for every primitive `h`-th root of unity, so the eigenvalues
  -- `ζ ^ eᵢ` of `c` are stable under inversion.
  obtain ⟨x, ζ, hx, hgx, hζ⟩ :=
    P.exists_isRegularWeight_bipartiteCoxeterElement_smul_eq_smul_isPrimitiveRoot b c
  have hchar {ξ : K} (hξ : IsPrimitiveRoot ξ (orderOf g)) :=
    P.charpoly_weylGroupRootRep_of_isRegularWeight_of_isPrimitiveRoot b hf hbij hx hgx hζ hξ
  have hsym := (hchar hζ).symm.trans (hchar hζ.inv)
  obtain ⟨l₁, l₂, -, -, hnd, hall, hw⟩ :=
    (weylCoxeterSystem P b).exists_wordProd_eq_bipartiteCoxeterElement c
  rw [weylCoxeterSystem_wordProd] at hw
  -- No exponent is divisible by `h`, since `1` is not an eigenvalue of `c`.
  have hdvd (k : κ) : ¬ orderOf g ∣ d k - 1 := fun hk ↦ by
    refine not_hasEigenvalue_one_wordProd b hnd hall ?_
    rw [hw, Module.End.hasEigenvalue_iff_isRoot_charpoly, hchar hζ, IsRoot.def, eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp [(hζ.pow_eq_one_iff_dvd _).2 hk])
  have hpair := hζ.two_mul_sum_mod_eq_mul_card hdvd hsym
  have hcard : Fintype.card κ = Module.finrank K M := by
    rw [← Nat.card_eq_fintype_card,
      P.natCard_eq_finrank_of_bijective_aeval_weylGroupRootRep_dual hbij]
  have hlen : (l₁ ++ l₂).length = Module.finrank K M := by
    rw [Module.finrank_eq_card_basis b.toWeightBasis, ← List.toFinset_card_of_nodup hnd,
      Finset.eq_univ_iff_forall.mpr fun i ↦ List.mem_toFinset.mpr (hall i), Finset.card_univ]
  have hle := natCard_le_orderOf_wordProd_mul_length b hnd hall
  rw [hw, hlen] at hle
  have hsum := P.sum_sub_one_eq_ncard_posRoots_of_bijective_aeval_weylGroupRootRep_dual b hf hbij
  have htwo := two_mul_ncard_posRoots P b
  have hmod : ∑ k, (d k - 1) % orderOf g ≤ ∑ k, (d k - 1) :=
    Finset.sum_le_sum fun k _ ↦ Nat.mod_le _ _
  rw [hcard] at hpair
  -- `2 ∑ (eᵢ % h) = r h ≥ |Φ| = 2 ∑ eᵢ ≥ 2 ∑ (eᵢ % h)`, so all are equal.
  have heq : ∑ k, (d k - 1) % orderOf g = ∑ k, (d k - 1) := by
    rw [mul_comm] at hle
    linarith
  refine ⟨by rw [mul_comm]; linarith, fun k ↦ ?_⟩
  have := (Finset.sum_eq_sum_iff_of_le fun k _ ↦ Nat.mod_le (d k - 1) (orderOf g)).mp heq k
    (Finset.mem_univ k)
  rw [← this]
  exact Nat.mod_lt _ (orderOf_pos g)

/-- **The exponents are less than the Coxeter number.** For a base of a finite irreducible reduced
crystallographic root system over an algebraically closed field containing `ℝ`, every exponent
`d k - 1` of a finite homogeneous basic invariant system of `Sym(M*)^W` is less than the order of
any Coxeter element. -/
theorem degree_sub_one_lt_orderOf_wordProd [Finite κ] (b : P.Base) {l : List b.support}
    (hl : l.Nodup) (hl' : ∀ i, i ∈ l)
    {f : κ → P.weylGroupRootRep.dual.symmetricAlgebraInvariants} {d : κ → ℕ}
    (hf : ∀ k, (f k : SymmetricAlgebra K (Module.Dual K M)) ∈
      homogeneousSubmodule K (Module.Dual K M) (d k))
    (hbij : Function.Bijective (MvPolynomial.aeval (R := K) f)) (k : κ) :
    d k - 1 < orderOf (wordProd P b l) := by
  have := P.finite_weight_of_isRootSystem
  obtain ⟨c⟩ := nonempty_coloring_graph_coxeterMatrixOfBase P b
  rw [← P.orderOf_bipartiteCoxeterElement_eq_orderOf_wordProd b c hl hl']
  exact (P.natCard_eq_and_degree_sub_one_lt_orderOf_bipartiteCoxeterElement b c hf hbij).2 k

section ExponentsAndEigenvalues

variable {ι K M N : Type*} [Field K] [CharZero K]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
  (P : RootPairing ι K M N) [Finite ι] [P.IsCrystallographic] [P.IsReduced]
  [P.IsRootSystem] [P.IsIrreducible]

private lemma map_supportEquiv_nodup_mem
    {ι R M N : Type*} [CommRing R] [CharZero R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] {P : RootPairing ι R M N} [P.IsCrystallographic]
    [P.IsRootSystem] (b : P.Base) (S : Type*) [CommRing S] [IsDomain S] [Algebra ℚ S]
    {l : List b.support} (hl : l.Nodup) (hall : ∀ i, i ∈ l) :
    let e := b.supportEquivRootPairingBaseChangeRationalModel S
    (l.map e.symm).Nodup ∧ ∀ j, j ∈ l.map e.symm :=
  ⟨hl.map (b.supportEquivRootPairingBaseChangeRationalModel S).symm.injective,
    fun j ↦ List.mem_map.2
      ⟨_, hall _, (b.supportEquivRootPairingBaseChangeRationalModel S).symm_apply_apply j⟩⟩

private lemma finite_of_bijective_aeval_weylGroupRootRep_dual (b : P.Base) {κ : Type*}
    {f : κ → P.weylGroupRootRep.dual.symmetricAlgebraInvariants}
    (hbij : Function.Bijective (MvPolynomial.aeval (R := K) f)) : Finite κ := by
  have : Nontrivial M := IsIrreducible.nontrivial P
  have : Module.Finite K M := Module.Finite.of_basis b.toWeightBasis
  have : Finite P.weylGroup := P.finite_weylGroup_of_base b
  exact Nat.finite_of_card_ne_zero
    ((P.natCard_eq_finrank_of_bijective_aeval_weylGroupRootRep_dual hbij).symm ▸
      Module.finrank_pos.ne')

omit [P.IsIrreducible] in
private lemma exists_complex_bijective_aeval_degrees_eq (b : P.Base)
    {κ : Type*} [Fintype κ]
    {f : κ → P.weylGroupRootRep.dual.symmetricAlgebraInvariants} {d : κ → ℕ}
    (hf : ∀ i, (f i : SymmetricAlgebra K (Module.Dual K M)) ∈
      homogeneousSubmodule K (Module.Dual K M) (d i))
    (hbij : Function.Bijective (MvPolynomial.aeval (R := K) f)) :
    ∃ (g : Fin (Module.finrank ℂ (b.support → ℂ)) →
        (rootPairingBaseChange ℂ b.rationalModel
          b.rationalModel_toLinearMap).weylGroupRootRep.dual.symmetricAlgebraInvariants)
      (e : Fin (Module.finrank ℂ (b.support → ℂ)) → ℕ),
      (∀ j, (g j : SymmetricAlgebra ℂ (Module.Dual ℂ (b.support → ℂ))) ∈
        homogeneousSubmodule ℂ (Module.Dual ℂ (b.support → ℂ)) (e j)) ∧
      Function.Bijective (MvPolynomial.aeval (R := ℂ) g) ∧
      Finset.univ.val.map d = Finset.univ.val.map e := by
  let PC := rootPairingBaseChange ℂ b.rationalModel b.rationalModel_toLinearMap
  let bC := rootPairingBaseChangeBase ℂ b.rationalModel b.rationalModel_toLinearMap
    b.rationalModelBase
  obtain ⟨g, hg_ex, hgbij⟩ := PC.exists_bijective_aeval_weylGroupRootRep_dual_of_base bC
  refine ⟨g, fun j ↦ (hg_ex j).choose, fun j ↦ (hg_ex j).choose_spec.2, hgbij, ?_⟩
  exact b.map_univ_eq_of_bijective_aeval_weylGroupRootRep_dual_rootPairingBaseChange_rationalModel
    ℂ hf hbij (fun j ↦ (hg_ex j).choose_spec.2) hgbij

/-- Packages the transfer of basic invariant degrees and the complex regular Coxeter eigenvector
to the complexified rational model `rootPairingBaseChange ℂ b.rationalModel`. -/
private lemma exists_complex_model_degrees_and_eigenvector (b : P.Base)
    {l : List b.support} (hl : l.Nodup) (hall : ∀ i, i ∈ l)
    {κ : Type*} [Fintype κ]
    {f : κ → P.weylGroupRootRep.dual.symmetricAlgebraInvariants} {d : κ → ℕ}
    (hf : ∀ i, (f i : SymmetricAlgebra K (Module.Dual K M)) ∈
      homogeneousSubmodule K (Module.Dual K M) (d i))
    (hbij : Function.Bijective (MvPolynomial.aeval (R := K) f)) :
    let PC := rootPairingBaseChange ℂ b.rationalModel b.rationalModel_toLinearMap
    let bC := rootPairingBaseChangeBase ℂ b.rationalModel b.rationalModel_toLinearMap
      b.rationalModelBase
    let lC := l.map (b.supportEquivRootPairingBaseChangeRationalModel ℂ).symm
    ∃ (g : Fin (Module.finrank ℂ (b.support → ℂ)) →
        PC.weylGroupRootRep.dual.symmetricAlgebraInvariants)
      (e : Fin (Module.finrank ℂ (b.support → ℂ)) → ℕ)
      (v : b.support → ℂ),
      (∀ j, (g j : SymmetricAlgebra ℂ (Module.Dual ℂ (b.support → ℂ))) ∈
        homogeneousSubmodule ℂ (Module.Dual ℂ (b.support → ℂ)) (e j)) ∧
      Function.Bijective (MvPolynomial.aeval (R := ℂ) g) ∧
      Finset.univ.val.map d = Finset.univ.val.map e ∧
      lC.Nodup ∧ (∀ j, j ∈ lC) ∧
      orderOf (wordProd PC bC lC) = orderOf (wordProd P b l) ∧
      PC.IsRegularWeight v ∧
      wordProd PC bC lC • v =
        (Complex.exp (2 * Real.pi * Complex.I / orderOf (wordProd P b l)))⁻¹ • v := by
  have : Nonempty b.support := b.nonempty_support_of_isIrreducible
  have : Nonempty ι := ⟨(Classical.arbitrary b.support : ι)⟩
  let PC := rootPairingBaseChange ℂ b.rationalModel b.rationalModel_toLinearMap
  let bC := rootPairingBaseChangeBase ℂ b.rationalModel b.rationalModel_toLinearMap
    b.rationalModelBase
  obtain ⟨hlC, hallC⟩ := map_supportEquiv_nodup_mem b ℂ hl hall
  obtain ⟨g, e, hg, hgbij, hmult⟩ := P.exists_complex_bijective_aeval_degrees_eq b hf hbij
  have hordC := (b.orderOf_wordProd_rootPairingBaseChange_rationalModel ℂ l).symm
  obtain ⟨v, hv_reg, hv_eig⟩ :=
    PC.exists_isRegularWeight_wordProd_smul_eq_inv_exp_smul bC hlC hallC
  rw [hordC] at hv_eig
  exact ⟨g, e, v, hg, hgbij, hmult, hlC, hallC, hordC, hv_reg, hv_eig⟩

/-- **Degree bounds for basic invariants of an irreducible crystallographic Weyl group.** Over
any characteristic-zero field, every basic invariant degree `d i` satisfies
`2 ≤ d i ≤ orderOf (wordProd P b l)`. -/
theorem two_le_and_le_orderOf_wordProd_of_bijective_aeval_weylGroupRootRep_dual (b : P.Base)
    {l : List b.support} (hl : l.Nodup) (hall : ∀ i, i ∈ l)
    {κ : Type*}
    {f : κ → P.weylGroupRootRep.dual.symmetricAlgebraInvariants} {d : κ → ℕ}
    (hf : ∀ i, (f i : SymmetricAlgebra K (Module.Dual K M)) ∈
      homogeneousSubmodule K (Module.Dual K M) (d i))
    (hbij : Function.Bijective (MvPolynomial.aeval (R := K) f)) (i : κ) :
    2 ≤ d i ∧ d i ≤ orderOf (wordProd P b l) := by
  have : Finite κ := P.finite_of_bijective_aeval_weylGroupRootRep_dual b hbij
  let := Fintype.ofFinite κ
  have : Nonempty b.support := b.nonempty_support_of_isIrreducible
  have : Nonempty ι := ⟨(Classical.arbitrary b.support : ι)⟩
  let PC := rootPairingBaseChange ℂ b.rationalModel b.rationalModel_toLinearMap
  let bC := rootPairingBaseChangeBase ℂ b.rationalModel b.rationalModel_toLinearMap
    b.rationalModelBase
  obtain ⟨hlC, hallC⟩ := map_supportEquiv_nodup_mem b ℂ hl hall
  obtain ⟨g, e, hg, hgbij, hmult⟩ := P.exists_complex_bijective_aeval_degrees_eq b hf hbij
  rcases Multiset.mem_map.1 (hmult ▸ Multiset.mem_map.2 ⟨i, Finset.mem_univ i, rfl⟩)
    with ⟨j, -, hj⟩
  have h2 : 2 ≤ e j := PC.two_le_of_injective_aeval_weylGroupRootRep_dual hg hgbij.1 j
  have hlt := PC.degree_sub_one_lt_orderOf_wordProd bC hlC hallC hg hgbij j
  rw [← b.orderOf_wordProd_rootPairingBaseChange_rationalModel ℂ l] at hlt
  omega

/-- **Exponent duality for irreducible crystallographic Weyl groups.** Over any characteristic-zero
field, the multiset of exponents `d i - 1` is invariant under
`m ↦ orderOf (wordProd P b l) - m`. -/
theorem map_sub_one_eq_map_orderOf_sub_of_bijective_aeval_weylGroupRootRep_dual (b : P.Base)
    {l : List b.support} (hl : l.Nodup) (hall : ∀ i, i ∈ l)
    {κ : Type*} [Fintype κ]
    {f : κ → P.weylGroupRootRep.dual.symmetricAlgebraInvariants} {d : κ → ℕ}
    (hf : ∀ i, (f i : SymmetricAlgebra K (Module.Dual K M)) ∈
      homogeneousSubmodule K (Module.Dual K M) (d i))
    (hbij : Function.Bijective (MvPolynomial.aeval (R := K) f)) :
    Finset.univ.val.map (fun i ↦ d i - 1) =
      Finset.univ.val.map (fun i ↦ orderOf (wordProd P b l) - (d i - 1)) := by
  classical
  have : Nontrivial M := IsIrreducible.nontrivial P
  have : Nonempty b.support := b.nonempty_support_of_isIrreducible
  have : Nonempty ι := ⟨(Classical.arbitrary b.support : ι)⟩
  set h : ℕ := orderOf (wordProd P b l)
  have hh2 : 2 ≤ h := P.two_le_orderOf_wordProd b hl hall
  have hh_pos : 0 < h := by omega
  have : NeZero h := ⟨hh_pos.ne'⟩
  let PC := rootPairingBaseChange ℂ b.rationalModel b.rationalModel_toLinearMap
  let bC := rootPairingBaseChangeBase ℂ b.rationalModel b.rationalModel_toLinearMap
    b.rationalModelBase
  obtain ⟨g, e, v, hg, hgbij, hmult, hlC, hallC, hordC, hv_reg, hv_eig⟩ :=
    P.exists_complex_model_degrees_and_eigenvector b hl hall hf hbij
  set ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / h)
  have hω : IsPrimitiveRoot ω h := Complex.isPrimitiveRoot_exp h hh_pos.ne'
  have hchar {ξ : ℂ} (hξ : IsPrimitiveRoot ξ h) :=
    PC.charpoly_weylGroupRootRep_of_isRegularWeight_of_isPrimitiveRoot bC hg hgbij hv_reg hv_eig
      hω.inv hξ
  have hprod : (∏ j, (X - C (ω ^ (e j - 1)))) = ∏ j, (X - C (ω⁻¹ ^ (e j - 1))) :=
    (hchar hω).symm.trans (hchar hω.inv)
  have he_pos (j) : 2 ≤ e j := PC.two_le_of_injective_aeval_weylGroupRootRep_dual hg hgbij.1 j
  have he_lt (j) : e j - 1 < h := by
    dsimp only [h]
    rw [← hordC]
    exact PC.degree_sub_one_lt_orderOf_wordProd bC hlC hallC hg hgbij j
  have hne0 (j) : ((e j - 1 : ℕ) : ZMod h) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    have := he_pos j
    exact Nat.not_dvd_of_pos_of_lt (by omega) (he_lt j)
  have hdualC : Finset.univ.val.map (fun j ↦ e j - 1) =
      Finset.univ.val.map (fun j ↦ h - (e j - 1)) := by
    have hval := congrArg (Multiset.map ZMod.val)
      (hω.map_neg_natCast_eq_of_prod_X_sub_C_pow_eq hprod)
    simpa only [Multiset.map_map, Function.comp_def, ZMod.val_natCast,
      Nat.mod_eq_of_lt (he_lt _), ZMod.neg_val, hne0, ↓reduceIte] using hval.symm
  have h1 := congrArg (Multiset.map (· - 1)) hmult
  have h2 := congrArg (Multiset.map (fun m ↦ h - (m - 1))) hmult
  simp only [Multiset.map_map, Function.comp_def] at h1 h2
  exact h1.trans (hdualC.trans h2.symm)

/-- **Crystallographic coprime-exponent theorem.** Over any characteristic-zero field, every
`a < orderOf (wordProd P b l)` coprime to `orderOf (wordProd P b l)` occurs as an exponent
`d i - 1`. -/
theorem exists_degree_sub_one_eq_of_coprime_orderOf_wordProd (b : P.Base)
    {l : List b.support} (hl : l.Nodup) (hall : ∀ i, i ∈ l)
    {κ : Type*}
    {f : κ → P.weylGroupRootRep.dual.symmetricAlgebraInvariants} {d : κ → ℕ}
    (hf : ∀ i, (f i : SymmetricAlgebra K (Module.Dual K M)) ∈
      homogeneousSubmodule K (Module.Dual K M) (d i))
    (hbij : Function.Bijective (MvPolynomial.aeval (R := K) f))
    {a : ℕ} (ha : a < orderOf (wordProd P b l)) (hcop : a.Coprime (orderOf (wordProd P b l))) :
    ∃ i : κ, d i - 1 = a := by
  have : Finite κ := P.finite_of_bijective_aeval_weylGroupRootRep_dual b hbij
  let := Fintype.ofFinite κ
  have : Nontrivial M := IsIrreducible.nontrivial P
  have : Nonempty b.support := b.nonempty_support_of_isIrreducible
  have : Nonempty ι := ⟨(Classical.arbitrary b.support : ι)⟩
  let PC := rootPairingBaseChange ℂ b.rationalModel b.rationalModel_toLinearMap
  let bC := rootPairingBaseChangeBase ℂ b.rationalModel b.rationalModel_toLinearMap
    b.rationalModelBase
  obtain ⟨g, e, v, hg, hgbij, hmult, hlC, hallC, hordC, hv_reg, hv_eig⟩ :=
    P.exists_complex_model_degrees_and_eigenvector b hl hall hf hbij
  set hC := orderOf (wordProd PC bC (l.map
    (b.supportEquivRootPairingBaseChangeRationalModel ℂ).symm))
  have : Finite P.weylGroup := P.finite_weylGroup_of_base b
  have hh_pos : 0 < hC := hordC.symm ▸ orderOf_pos (wordProd P b l)
  have hω_inv : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / hC))⁻¹ hC :=
    (Complex.isPrimitiveRoot_exp hC hh_pos.ne').inv
  have he_lt (j) : e j - 1 < hC := PC.degree_sub_one_lt_orderOf_wordProd bC hlC hallC hg hgbij j
  rw [← hordC] at hv_eig ha hcop
  obtain ⟨j, hj⟩ := PC.exists_degree_sub_one_eq_of_isRegularWeight_of_isPrimitiveRoot bC hg hgbij
    hv_reg hv_eig hω_inv he_lt ha hcop
  rcases Multiset.mem_map.1 (hmult.symm ▸ Multiset.mem_map.2 ⟨j, Finset.mem_univ j, rfl⟩)
    with ⟨i, -, hi⟩
  exact ⟨i, hi ▸ hj⟩

/-- **Existence of a quadratic basic invariant.** Over any characteristic-zero field, every
finite homogeneous basic invariant system of an irreducible crystallographic Weyl group contains a
degree-`2` invariant. -/
theorem exists_degree_eq_two_of_bijective_aeval_weylGroupRootRep_dual
    {κ : Type*}
    {f : κ → P.weylGroupRootRep.dual.symmetricAlgebraInvariants} {d : κ → ℕ}
    (hf : ∀ i, (f i : SymmetricAlgebra K (Module.Dual K M)) ∈
      homogeneousSubmodule K (Module.Dual K M) (d i))
    (hbij : Function.Bijective (MvPolynomial.aeval (R := K) f)) :
    ∃ i : κ, d i = 2 := by
  obtain ⟨b⟩ := P.nonempty_base
  have : Nontrivial M := IsIrreducible.nontrivial P
  have hl := Finset.nodup_toList (Finset.univ : Finset b.support)
  have hh2 := P.two_le_orderOf_wordProd b hl (fun j ↦ by simp)
  obtain ⟨i, hi⟩ := P.exists_degree_sub_one_eq_of_coprime_orderOf_wordProd b hl
    (fun j ↦ by simp) hf hbij (a := 1) (by omega) (Nat.coprime_one_left _)
  exact ⟨i, by omega⟩

/-- **The Coxeter number is a basic invariant degree.** Over any characteristic-zero field, some
`d i` equals `orderOf (wordProd P b l)`; together with
`two_le_and_le_orderOf_wordProd_of_bijective_aeval_weylGroupRootRep_dual` it is the largest. -/
theorem exists_degree_eq_orderOf_wordProd_of_bijective_aeval_weylGroupRootRep_dual (b : P.Base)
    {l : List b.support} (hl : l.Nodup) (hall : ∀ i, i ∈ l)
    {κ : Type*}
    {f : κ → P.weylGroupRootRep.dual.symmetricAlgebraInvariants} {d : κ → ℕ}
    (hf : ∀ i, (f i : SymmetricAlgebra K (Module.Dual K M)) ∈
      homogeneousSubmodule K (Module.Dual K M) (d i))
    (hbij : Function.Bijective (MvPolynomial.aeval (R := K) f)) :
    ∃ i : κ, d i = orderOf (wordProd P b l) := by
  have : Nontrivial M := IsIrreducible.nontrivial P
  have hh2 : 2 ≤ orderOf (wordProd P b l) := P.two_le_orderOf_wordProd b hl hall
  have hcop : (orderOf (wordProd P b l) - 1).Coprime (orderOf (wordProd P b l)) :=
    (Nat.coprime_self_sub_left (by omega)).2 (Nat.coprime_one_left _)
  obtain ⟨i, hi⟩ := P.exists_degree_sub_one_eq_of_coprime_orderOf_wordProd b hl hall hf hbij
    (a := orderOf (wordProd P b l) - 1) (by omega) hcop
  exact ⟨i, by omega⟩

/-- **Characteristic polynomial of a Coxeter element from basic invariant degrees.** Over any
characteristic-zero field `K` and any primitive `h`-th root of unity `ζ : K` where
`h = orderOf (wordProd P b l)`, the characteristic polynomial of
`P.weylGroupRootRep (wordProd P b l)` is `∏ i, (X - C (ζ ^ (d i - 1)))`. -/
theorem charpoly_weylGroupRootRep_wordProd_eq_prod [Module.Finite K M] (b : P.Base)
    {l : List b.support} (hl : l.Nodup) (hall : ∀ i, i ∈ l)
    {κ : Type*} [Fintype κ]
    {f : κ → P.weylGroupRootRep.dual.symmetricAlgebraInvariants} {d : κ → ℕ}
    (hf : ∀ i, (f i : SymmetricAlgebra K (Module.Dual K M)) ∈
      homogeneousSubmodule K (Module.Dual K M) (d i))
    (hbij : Function.Bijective (MvPolynomial.aeval (R := K) f))
    {ζ : K} (hζ : IsPrimitiveRoot ζ (orderOf (wordProd P b l))) :
    (P.weylGroupRootRep (wordProd P b l)).charpoly = ∏ i : κ, (X - C (ζ ^ (d i - 1))) := by
  classical
  have : Nontrivial M := IsIrreducible.nontrivial P
  have : Nonempty b.support := b.nonempty_support_of_isIrreducible
  have : Nonempty ι := ⟨(Classical.arbitrary b.support : ι)⟩
  set h : ℕ := orderOf (wordProd P b l)
  have hh2 : 2 ≤ h := P.two_le_orderOf_wordProd b hl hall
  have hh_pos : 0 < h := by omega
  let PC := rootPairingBaseChange ℂ b.rationalModel b.rationalModel_toLinearMap
  let bC := rootPairingBaseChangeBase ℂ b.rationalModel b.rationalModel_toLinearMap
    b.rationalModelBase
  obtain ⟨g, e, v, hg, hgbij, hmult, -, -, -, hv_reg, hv_eig⟩ :=
    P.exists_complex_model_degrees_and_eigenvector b hl hall hf hbij
  set ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / h)
  have hω : IsPrimitiveRoot ω h := Complex.isPrimitiveRoot_exp h hh_pos.ne'
  have hcharC := PC.charpoly_weylGroupRootRep_of_isRegularWeight_of_isPrimitiveRoot bC hg hgbij
    hv_reg hv_eig hω.inv hω
  let p : ℚ[X] := ((l.map (reflMatrix b.cartanMatrix)).prod.map (Int.castRingHom ℚ)).charpoly
  have hprodC : p.map (algebraMap ℚ ℂ) = ∏ i : κ, (X - C (ω ^ (d i - 1))) := by
    dsimp only [p]
    dsimp only [PC, bC] at hcharC
    rw [b.charpoly_weylGroupRootRep_wordProd_rootPairingBaseChange_rationalModel ℂ l, hcharC,
      Finset.prod_eq_multiset_prod, Finset.prod_eq_multiset_prod]
    have hmap := congrArg (Multiset.map (fun m ↦ X - C (ω ^ (m - 1)))) hmult
    simp only [Multiset.map_map, Function.comp_def] at hmap
    exact congrArg Multiset.prod hmap.symm
  dsimp only [p] at hprodC
  rw [← b.charpoly_weylGroupRootRep_wordProd_eq_map_rat l]
  exact hω.map_eq_prod_of_map_eq_prod hh_pos hζ hprodC

end ExponentsAndEigenvalues

end RootPairing
