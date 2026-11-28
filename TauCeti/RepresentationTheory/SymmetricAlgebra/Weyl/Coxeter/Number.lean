/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Coxeter.Element.Conj
public import TauCeti.LinearAlgebra.RootSystem.Coxeter.Element.Orbit
public import TauCeti.LinearAlgebra.RootSystem.Coxeter.Number
public import TauCeti.RepresentationTheory.SymmetricAlgebra.Weyl.CoprimeExponents
public import TauCeti.RepresentationTheory.SymmetricAlgebra.Weyl.Coxeter.Element
public import TauCeti.RingTheory.Polynomial.Cyclotomic.Exponents
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import TauCeti.LinearAlgebra.RootSystem.Basic
import TauCeti.RingTheory.Polynomial.Roots
import TauCeti.RingTheory.RootsOfUnity.Complex.Exp

/-!
# The Coxeter number and the exponents of a Weyl group

Let `b` be a base of a finite irreducible reduced crystallographic root system of rank `r`, on a
finite-dimensional space over an algebraically closed field `K` containing `ℝ`, such as `ℂ`. Let
`c` be a Coxeter element, a product of the `r` simple reflections in some order, and let `h` be
its order, the **Coxeter number**. This file proves:

* the number of roots is `|Φ| = r h`, equivalently `|Φ⁺| = r h / 2`;
* every exponent `dᵢ - 1`, for the degrees `dᵢ` of a homogeneous basic invariant system, is less
  than `h`;
* the multiset of basic-invariant exponents `dᵢ - 1` equals `(classifiedDynkinType b).exponents`,
  and the multiset of invariant degrees `dᵢ` equals `(classifiedDynkinType b).degrees`.

With the computation of the eigenvalues of the bipartite Coxeter element at a regular
eigenvector (`RootPairing.exists_isPrimitiveRoot_charpoly_bipartiteCoxeterElement_eq_prod`), the
second statement says that its eigenvalues are `ζ ^ eᵢ` for a primitive `h`-th root of unity `ζ`,
with exponents `1 ≤ eᵢ < h` (the lower bound is
`RootPairing.two_le_of_injective_aeval_weylGroupRootRep_dual`). Comparing this rational
characteristic polynomial with its complex eigenvalue multiset from
`TauCeti.HasCartanType.roots_charpoly_of_actsBy` then identifies the basic-invariant exponents and
degrees with the Dynkin-type lists `exponents` and `degrees`.

## The argument

The bipartite Coxeter element `c` has a regular eigenvector for a primitive `h`-th root of unity
`ζ`, and since its characteristic polynomial is rational, the eigenvalue computation there holds
with `ζ` replaced by any primitive `h`-th root of unity
(`RootPairing.charpoly_weylGroupRootRep_of_isRegularWeight_of_isPrimitiveRoot`). Using `ζ` and
`ζ⁻¹` shows that the exponents `eᵢ` modulo `h` are stable under `e ↦ -e`, with multiplicity.
None of them is `0` modulo `h`, as `1` is not an eigenvalue of `c`, so they pair off and
`2 ∑ᵢ (eᵢ % h) = r h`. On the other hand `∑ᵢ eᵢ = |Φ⁺|`
(`RootPairing.sum_sub_one_eq_ncard_posRoots_of_bijective_aeval_weylGroupRootRep_dual`) and every
`⟨c⟩`-orbit of roots meets the inversion set of `c`, which has `r` elements, within `h` steps,
so `2 |Φ⁺| = |Φ| ≤ r h` (`TauCeti.natCard_le_orderOf_wordProd_mul_length`). As `eᵢ % h ≤ eᵢ`,
all these inequalities are equalities: `|Φ| = r h` and `eᵢ % h = eᵢ`. Since all Coxeter elements
are conjugate, the results hold for every Coxeter element.

## Main results

* `RootPairing.natCard_eq_finrank_mul_orderOf_wordProd`: the number of roots is the rank times the
  order of any Coxeter element.
* `RootPairing.degree_sub_one_lt_orderOf_wordProd`: every exponent `dᵢ - 1` of a homogeneous basic
  invariant system is less than the order of any Coxeter element.
* `RootPairing.map_sub_one_eq_exponents_classifiedDynkinType`: the multiset of exponents `dᵢ - 1`
  of any homogeneous basic invariant system equals
  `Multiset.ofList (classifiedDynkinType b).exponents`.
* `RootPairing.map_eq_degrees_classifiedDynkinType`: the multiset of degrees `dᵢ` of any
  homogeneous basic invariant system equals `Multiset.ofList (classifiedDynkinType b).degrees`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. V, §6, no. 2.
* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, Cambridge University Press (1990),
  §§3.18–3.20.
* T. A. Springer, *Regular elements of finite reflection groups*, Invent. Math. **25** (1974),
  159–198, §4.
-/

public section

open Polynomial SymmetricAlgebra TauCeti TauCeti.SymmetricAlgebra

namespace RootPairing

variable {ι K M N κ : Type*} [Field K] [CharZero K] [Algebra ℝ K] [IsAlgClosed K]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
  (P : RootPairing ι K M N) [Finite ι] [Nonempty ι] [P.IsCrystallographic] [P.IsReduced]
  [P.IsIrreducible]

/-- The two results of this file for the bipartite Coxeter element: `|Φ| = r h` and `eᵢ < h`. -/
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

/-- **The Coxeter number is the number of roots divided by the rank.** For a base of a finite
irreducible reduced crystallographic root system over an algebraically closed field containing
`ℝ`, the number of roots is the rank `r` times the order `h`
of any Coxeter element, a product of all the simple reflections, each exactly once. Equivalently
(`TauCeti.two_mul_ncard_posRoots`), there are `r h / 2` positive roots. -/
theorem natCard_eq_finrank_mul_orderOf_wordProd (b : P.Base) {l : List b.support}
    (hl : l.Nodup) (hl' : ∀ i, i ∈ l) :
    Nat.card ι = Module.finrank K M * orderOf (wordProd P b l) := by
  have := P.finite_weight_of_isRootSystem
  obtain ⟨f, hfd, hbij⟩ := P.exists_bijective_aeval_weylGroupRootRep_dual_of_base b
  choose d _ hd using hfd
  obtain ⟨c⟩ := nonempty_coloring_graph_coxeterMatrixOfBase P b
  rw [← P.orderOf_bipartiteCoxeterElement_eq_orderOf_wordProd b c hl hl']
  exact (P.natCard_eq_and_degree_sub_one_lt_orderOf_bipartiteCoxeterElement b c hd hbij).1

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

/-- Transfer a factorization `p = ∏ i, (X - ζ ^ e i)` from a primitive `h`-th root of unity in one
rational domain to a primitive `h`-th root of unity in another. -/
private theorem map_eq_prod_of_map_eq_prod {K₁ K₂ ι' : Type*} [CommRing K₁] [IsDomain K₁]
    [Algebra ℚ K₁] [CommRing K₂] [IsDomain K₂] [Algebra ℚ K₂] [Fintype ι'] {h : ℕ} (hh : 0 < h)
    {ζ : K₁} {ξ : K₂} (hζ : IsPrimitiveRoot ζ h) (hξ : IsPrimitiveRoot ξ h) {p : ℚ[X]}
    {e : ι' → ℕ} (hprod : p.map (algebraMap ℚ K₁) = ∏ i, (X - C (ζ ^ e i))) :
    p.map (algebraMap ℚ K₂) = ∏ i, (X - C (ξ ^ e i)) := by
  have : NeZero (h : ℚ) := ⟨Nat.cast_ne_zero.mpr hh.ne'⟩
  let F : ℚ[X][X] := ∏ i, (X - C (X ^ e i))
  have hF₁ : F.map (aeval ζ).toRingHom = ∏ i, (X - C (ζ ^ e i)) := by
    simp [F, Polynomial.map_prod]
  have hF₂ : F.map (aeval ξ).toRingHom = ∏ i, (X - C (ξ ^ e i)) := by
    simp [F, Polynomial.map_prod]
  ext j
  have hj := congr(($hprod).coeff j)
  rw [← hF₁, coeff_map, coeff_map] at hj
  rw [← hF₂, coeff_map, coeff_map]
  obtain ⟨q, hq⟩ : cyclotomic h ℚ ∣ F.coeff j - C (p.coeff j) := by
    rw [hζ.minpoly_eq_cyclotomic_of_irreducible (cyclotomic.irreducible_rat hh)]
    exact minpoly.dvd ℚ ζ (by simpa [sub_eq_zero] using hj.symm)
  have hcy : aeval ξ (cyclotomic h ℚ) = 0 := by
    rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic]
    exact (hξ.isRoot_cyclotomic hh).eq_zero
  have hξq := congr(aeval ξ $hq)
  rw [map_mul, hcy, zero_mul, map_sub, aeval_C, sub_eq_zero] at hξq
  simpa using hξq.symm

/-- **The basic-invariant exponents of `Sym(M*)^W` equal the exponents of the classified Dynkin
type.** For any base `b` of a finite irreducible reduced crystallographic root system over an
algebraically closed field containing `ℝ`, and any finite homogeneous basic invariant system of
`Sym(M*)^W` with degrees `d`, the multiset of exponents `d k - 1` equals
`Multiset.ofList (classifiedDynkinType b).exponents`. -/
theorem map_sub_one_eq_exponents_classifiedDynkinType [Fintype κ] (b : P.Base)
    {f : κ → P.weylGroupRootRep.dual.symmetricAlgebraInvariants} {d : κ → ℕ}
    (hf : ∀ k, (f k : SymmetricAlgebra K (Module.Dual K M)) ∈
      homogeneousSubmodule K (Module.Dual K M) (d k))
    (hbij : Function.Bijective (MvPolynomial.aeval (R := K) f)) :
    Finset.univ.val.map (fun k ↦ d k - 1) = Multiset.ofList (classifiedDynkinType b).exponents := by
  classical
  have := P.finite_weight_of_isRootSystem
  obtain ⟨c⟩ := nonempty_coloring_graph_coxeterMatrixOfBase P b
  let g := (weylCoxeterSystem P b).bipartiteCoxeterElement c
  have := P.finite_weylGroup_of_base b
  obtain ⟨x, ζ, hx, hgx, hζ⟩ :=
    P.exists_isRegularWeight_bipartiteCoxeterElement_smul_eq_smul_isPrimitiveRoot b c
  have hchar := P.charpoly_weylGroupRootRep_of_isRegularWeight_of_isPrimitiveRoot b hf hbij hx hgx
    hζ hζ
  obtain ⟨l₁, l₂, -, -, hnd, hall, hw⟩ :=
    (weylCoxeterSystem P b).exists_wordProd_eq_bipartiteCoxeterElement c
  rw [weylCoxeterSystem_wordProd] at hw
  set l := l₁ ++ l₂
  let t := classifiedDynkinType b
  have ht : t.Valid := valid_classifiedDynkinType b
  have hct : HasCartanType P b t := hasCartanType_classifiedDynkinType b
  have hh : orderOf g = t.coxeterNumber := by
    change orderOf ((weylCoxeterSystem P b).bipartiteCoxeterElement c) = t.coxeterNumber
    rw [← hw]
    exact b.orderOf_wordProd_eq_coxeterNumber_classifiedDynkinType hnd hall
  have hpos : 0 < orderOf g := orderOf_pos g
  let W : Matrix b.support b.support ℤ := (l.map b.cartanMatrix.reflMatrix).prod
  let q : ℚ[X] := W.charpoly.map (Int.castRingHom ℚ)
  have hqC : q.map (algebraMap ℚ ℂ) = (W.map (Int.castRingHom ℂ)).charpoly := by
    rw [Polynomial.map_map,
      Subsingleton.elim ((algebraMap ℚ ℂ).comp (Int.castRingHom ℚ)) (Int.castRingHom ℂ),
      Matrix.charpoly_map]
  have hqK : q.map (algebraMap ℚ K) = (P.weylGroupRootRep g).charpoly := by
    change q.map (algebraMap ℚ K) =
      (P.weylGroupRootRep ((weylCoxeterSystem P b).bipartiteCoxeterElement c)).charpoly
    rw [← hw, (b.actsBy_wordProd l).charpoly_weylGroupRootRep, Polynomial.map_map,
      Subsingleton.elim ((algebraMap ℚ K).comp (Int.castRingHom ℚ)) (Int.castRingHom K)]
  have hroots : (W.map (Int.castRingHom ℂ)).charpoly.roots =
      Multiset.ofList (t.exponents.map fun e : ℕ =>
        Complex.exp (2 * Real.pi * Complex.I * ((e : ℂ) / (orderOf g : ℂ)))) := by
    rw [hh]
    exact hct.roots_charpoly_of_actsBy ht hnd hall (b.actsBy_wordProd l)
  simp_rw [← exp_two_pi_I_div_pow (orderOf g : ℂ)] at hroots
  set ζ₀ : ℂ := Complex.exp (2 * Real.pi * Complex.I / (orderOf g : ℂ))
  have hζ₀ : IsPrimitiveRoot ζ₀ (orderOf g) := Complex.isPrimitiveRoot_exp _ hpos.ne'
  have hcard : (W.map (Int.castRingHom ℂ)).charpoly.roots.card =
      (W.map (Int.castRingHom ℂ)).charpoly.natDegree := by
    rw [hroots, Multiset.coe_card, List.length_map, t.length_exponents,
      Matrix.charpoly_natDegree_eq_dim]
    exact hct.card_support.symm.trans (Fintype.card_coe b.support).symm
  have hprodC : q.map (algebraMap ℚ ℂ) =
      ∏ i : Fin t.exponents.length, (X - C (ζ₀ ^ t.exponents[i])) := by
    rw [hqC, ← prod_multiset_X_sub_C_of_monic_of_roots_card_eq (Matrix.charpoly_monic _) hcard,
      hroots, Multiset.map_coe, Multiset.prod_coe, List.map_map]
    conv_lhs => rw [← List.ofFn_getElem (xs := t.exponents), List.map_ofFn, Fin.prod_ofFn]
    rfl
  have hprodK := map_eq_prod_of_map_eq_prod hpos hζ₀ hζ hprodC
  rw [hqK, hchar] at hprodK
  have hrootsEq := congrArg Polynomial.roots hprodK
  simp only [roots_prod_X_sub_C_map] at hrootsEq
  let s₁ : Multiset ℕ := Finset.univ.val.map fun k ↦ d k - 1
  let s₂ : Multiset ℕ := Finset.univ.val.map fun i : Fin t.exponents.length ↦ t.exponents[i]
  have hs₂ : s₂ = Multiset.ofList t.exponents := by
    dsimp only [s₂]
    rw [Fin.univ_val_map]
    exact congrArg Multiset.ofList List.ofFn_getElem
  rw [← hs₂]
  have hlt₁ : ∀ a ∈ s₁, a < orderOf g := by
    intro a ha
    rw [Multiset.mem_map] at ha
    obtain ⟨k, -, rfl⟩ := ha
    change d k - 1 < orderOf ((weylCoxeterSystem P b).bipartiteCoxeterElement c)
    rw [← hw]
    exact P.degree_sub_one_lt_orderOf_wordProd b hnd hall hf hbij k
  have hlt₂ : ∀ a ∈ s₂, a < orderOf g := by
    intro a ha
    rw [hs₂, Multiset.mem_coe] at ha
    exact hh ▸ t.lt_coxeterNumber_of_mem_exponents ht ha
  refine Multiset.ext.mpr fun a ↦ ?_
  by_cases ha : a < orderOf g
  · have hc (s : Multiset ℕ) (hs : ∀ b ∈ s, b < orderOf g) :
        (s.map (ζ ^ ·)).count (ζ ^ a) = s.count a := by
      simp only [Multiset.count_eq_card_filter_eq, Multiset.filter_map]
      rw [Multiset.card_map]
      congr 1
      exact Multiset.filter_congr fun b hb ↦ by
        simp only [Function.comp_apply]
        exact ⟨fun hb' ↦ hζ.pow_inj ha (hs b hb) hb', fun hb' ↦ hb' ▸ rfl⟩
    have hmap : s₁.map (ζ ^ ·) = s₂.map (ζ ^ ·) := by
      simpa [s₁, s₂, Multiset.map_map, Function.comp_def] using hrootsEq
    rw [← hc s₁ hlt₁, ← hc s₂ hlt₂, hmap]
  · rw [Multiset.count_eq_zero.mpr (fun h ↦ ha (hlt₁ a h)),
      Multiset.count_eq_zero.mpr (fun h ↦ ha (hlt₂ a h))]

/-- **The basic invariant degrees of `Sym(M*)^W` equal the fundamental degrees of the classified
Dynkin type.** For any base `b` of a finite irreducible reduced crystallographic root system over
an algebraically closed field containing `ℝ`, and any finite homogeneous basic invariant system of
`Sym(M*)^W` with degrees `d`, the multiset of degrees `d k` equals
`Multiset.ofList (classifiedDynkinType b).degrees`. -/
theorem map_eq_degrees_classifiedDynkinType [Fintype κ] (b : P.Base)
    {f : κ → P.weylGroupRootRep.dual.symmetricAlgebraInvariants} {d : κ → ℕ}
    (hf : ∀ k, (f k : SymmetricAlgebra K (Module.Dual K M)) ∈
      homogeneousSubmodule K (Module.Dual K M) (d k))
    (hbij : Function.Bijective (MvPolynomial.aeval (R := K) f)) :
    Finset.univ.val.map d = Multiset.ofList (classifiedDynkinType b).degrees := by
  have heq : (Finset.univ.val.map (fun k ↦ d k - 1)).map (· + 1) =
      (Multiset.ofList (classifiedDynkinType b).exponents).map (· + 1) :=
    congrArg (Multiset.map (· + 1)) (P.map_sub_one_eq_exponents_classifiedDynkinType b hf hbij)
  rw [Multiset.map_coe, ← DynkinType.degrees_def, Multiset.map_map] at heq
  refine (Multiset.map_congr rfl fun k _ ↦ ?_).symm.trans heq
  have h2 := P.two_le_of_injective_aeval_weylGroupRootRep_dual hf hbij.injective k
  dsimp only [Function.comp_apply]
  omega

end RootPairing
