/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.GroupAction.TypeTags
public import TauCeti.Topology.Algebra.ContinuousMonoidHom.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.NormalForm.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.CompletedGroupAlgebraModule
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Subgroup

/-!
# The relator classes of the Demushkin normal forms in Labute's module

Let `G` be a pro-`p` group, `N` a closed normal subgroup, and `N^{ab} = N ⧸ (N, N)` its topological
abelianization, a compact module over the completed group algebra `Λ = ℤ_p[[G ⧸ N]]` through the
conjugation action `[g] • [x] = [g x g⁻¹]` (`TauCeti.IsProP.completedGroupAlgebraModule`). This
file computes the classes in `N^{ab}` of the three Demushkin normal-form relator words of
`TauCeti.Topology.Algebra.Group.Profinite.Demushkin.NormalForm.Basic`, read on a tuple `x` whose
entries occurring in the word, other than the marked generators, lie in `N`, as explicit
`Λ`-combinations of the classes of the entries lying in `N`.

The computation rests on two facts about classes in `N^{ab}`. Labute's commutator
`(x, g) = x⁻¹ (g⁻¹ x g)` of `x ∈ N` with `g ∈ G` has class `([g]⁻¹ - 1) • [x]`
(`TauCeti.IsProP.ofMul_mk_labuteComm`), so the marked factor `x^k (x, g)` has class
`(k - 1 + [g]⁻¹) • [x]` (`TauCeti.IsProP.ofMul_mk_pow_mul_labuteComm`), and a commutator of two
elements of `N` has class zero (`TopologicalAbelianization.ofMul_mk_eq_zero_of_mem_commutator`).
Hence, writing `[x_i]` for the class of a generator and `[x_i]` inside a coefficient for its image
in `Λ`, and `m = n / 2` for the number of commutator factors of the words (so that the last
pair is `(x_{n-1}, x_n)` when `n` has the parity of the normal form in question), the words have
the classes

* `x₁^q (x₁, x₂)(x₃, x₄) ⋯ (x_{2m-1}, x_{2m}) ↦ (q - 1 + [x₂]⁻¹) • [x₁]`, for `x_i ∈ N` when
  `i ≤ 2m`, `i ≠ 2`;
* `x₁² x₂^{2^f} (x₂, x₃)(x₄, x₅) ⋯ (x_{2m}, x_{2m+1}) ↦ [x₁²] + (2^f - 1 + [x₃]⁻¹) • [x₂]`, for
  `x₁² ∈ N` and `x_i ∈ N` when `i ≤ 2m + 1`, `i ≠ 1, 3`;
* `x₁^{2+a} (x₁, x₂) x₃^{2^f} (x₃, x₄) ⋯ (x_{2m-1}, x_{2m}) ↦ (1 + a + [x₂]⁻¹) • [x₁] +
  (2^f - 1 + [x₄]⁻¹) • [x₃]`, for `x_i ∈ N` when `i ≤ 2m`, `i ≠ 2, 4`, and `n ≥ 4`; for `n ≤ 3`
  the word is `x₁^{2+a} (x₁, x₂) x₃^{2^f}`, and the second coefficient is `2^f`.

The entries of `x` beyond those occurring in a word do not enter its hypotheses. The membership
of the words themselves in `N` is `TauCeti.demushkinWordNeTwo_mem` and its companions, which ask
only for the power factors and the left entries of the commutators.

The case of interest is `N = X = ker χ` for a continuous character `χ : G → ℤ_pˣ`, with the
membership hypotheses read as `χ (x_i) = 1`; the second half of the file states the three
computations in that form. For `G` free pro-`p` on `x₁, …, x_n` and `χ` the standard orientation
of a normal form, which is trivial on the unmarked generators
(`TauCeti.orientationNeTwo_presentedProPGen_of_ne` and its companions, composed with the
presentation map), `X^{ab}` is Labute's module `E = X ⧸ (X, X)` (§4 Definition, p. 121), and the
third formula is his expression of the relator class in the dyadic even-rank case (p. 122), which
in his letters reads `⟦r⟧ = (1 + a + (1 + T)^a) ⟦y₁⟧ + (2^g + (1 + T)^{ab} - 1) ⟦y₃⟧`. There his
`2^g` is the `2^f` of this file, `1 + T` is a topological generator of `Λ = ℤ₂[[Γ]]`,
`Γ = Im χ`, and `(1 + T)^a`, `(1 + T)^{ab}` are the images `[x₂]`, `[x₄]` of the marked
generators in `Γ`, written as powers of that generator; the exponents `a`, `ab` of `1 + T` are
Labute's names for those images and are not the exponent `a` of the word. In the letters of this
file his formula reads `(1 + a + [x₂]) ⟦y₁⟧ + (2^f + [x₄] - 1) ⟦y₃⟧`.

**Conventions.** Labute lets `Γ` act by `[y] · [x] = [y⁻¹ x y]`, the inverse of the conjugation
action used here (see `TopologicalAbelianization.mk_inv_smul_mk`); accordingly, every coefficient
below carries `[g]⁻¹` where Labute writes `[g]`. The exponents `q`, `2 + a` and `2^f` are natural
numbers, as in the definitions of the words.

## Main results

* `TauCeti.IsProP.ofMul_mk_labuteComm`: the class of Labute's commutator `(x, g)`, `x ∈ N`, is
  `([g]⁻¹ - 1) • [x]`.
* `TauCeti.IsProP.ofMul_mk_pow_mul_labuteComm`: the class of `x^k (x, g)`, `x ∈ N`, is
  `(k - 1 + [g]⁻¹) • [x]`.
* `TauCeti.IsProP.ofMul_mk_demushkinWordNeTwo`, `TauCeti.IsProP.ofMul_mk_demushkinWordTwoOdd`,
  `TauCeti.IsProP.ofMul_mk_demushkinWordTwoEven`,
  `TauCeti.IsProP.ofMul_mk_demushkinWordTwoEven_of_le_three`: the relator classes of the three
  normal-form words in `N^{ab}`, for a tuple whose unmarked entries occurring in the word lie in
  `N`.
* `TauCeti.IsProP.ofMul_mk_demushkinWordNeTwo_ker`,
  `TauCeti.IsProP.ofMul_mk_demushkinWordTwoOdd_ker`,
  `TauCeti.IsProP.ofMul_mk_demushkinWordTwoEven_ker`,
  `TauCeti.IsProP.ofMul_mk_demushkinWordTwoEven_ker_of_le_three`: the same in the abelianized
  kernel of a continuous character trivial on the unmarked generators occurring in the word.

## References

* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), 106–132, §4,
  pp. 121–122.
-/

public section

namespace TauCeti

open scoped commutatorElement

/-! ### The relator classes over the completed group algebra -/

namespace IsProP

section Module

variable {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G] (hG : IsProP p G) {N : Subgroup G} [N.Normal]
  [IsClosed (N : Set G)]
include hG

/-- **The class of Labute's commutator `(x, g)`, for `x ∈ N`**, in `N^{ab}` as a module over
`ℤ_p[[G ⧸ N]]`: it is `([g]⁻¹ - 1) • [x]`, for the conjugation action `[g] • [x] = [g x g⁻¹]`
of `TauCeti.IsProP.completedGroupAlgebraModule`. In Labute's convention `[g] · [x] = [g⁻¹ x g]`
the coefficient reads `[g] - 1`. -/
theorem ofMul_mk_labuteComm {x : G} (hx : x ∈ N) (g : G) :
    letI := (hG.topologicalAbelianization N).completedGroupAlgebraModule (G ⧸ N)
    Additive.ofMul ((⟨labuteComm x g, labuteComm_mem_of_mem_left hx g⟩ : N) :
        TopologicalAbelianization N) =
      (completedGroupAlgebra.of ℤ_[p] (G ⧸ N) (g : G ⧸ N)⁻¹ - 1) •
        Additive.ofMul ((⟨x, hx⟩ : N) : TopologicalAbelianization N) := by
  let _ := (hG.topologicalAbelianization N).completedGroupAlgebraModule (G ⧸ N)
  have h : (⟨labuteComm x g, labuteComm_mem_of_mem_left hx g⟩ : N) =
      (⟨x, hx⟩ : N)⁻¹ * ⟨g⁻¹ * ((⟨x, hx⟩ : N) : G) * g, ‹N.Normal›.conj_mem' _ hx g⟩ :=
    Subtype.ext (by simp [labuteComm_def, mul_assoc])
  rw [h, QuotientGroup.mk_mul, QuotientGroup.mk_inv, ofMul_mul, ofMul_inv, neg_add_eq_sub,
    sub_smul, one_smul, (hG.topologicalAbelianization N).completedGroupAlgebraModule_of_smul,
    ← Additive.ofMul_smul, TopologicalAbelianization.mk_inv_smul_mk]

/-- **The class of the marked factor `x^k (x, g)`, for `x ∈ N`**, in `N^{ab}` as a module over
`ℤ_p[[G ⧸ N]]`: it is `(k - 1 + [g]⁻¹) • [x]`. Each marked generator of a normal-form word enters
through a factor of this shape. -/
theorem ofMul_mk_pow_mul_labuteComm {x : G} (hx : x ∈ N) (g : G) (k : ℕ) :
    letI := (hG.topologicalAbelianization N).completedGroupAlgebraModule (G ⧸ N)
    Additive.ofMul ((⟨x ^ k * labuteComm x g,
        mul_mem (pow_mem hx k) (labuteComm_mem_of_mem_left hx g)⟩ : N) :
          TopologicalAbelianization N) =
      ((k : completedGroupAlgebra ℤ_[p] (G ⧸ N)) - 1 +
          completedGroupAlgebra.of ℤ_[p] (G ⧸ N) (g : G ⧸ N)⁻¹) •
        Additive.ofMul ((⟨x, hx⟩ : N) : TopologicalAbelianization N) := by
  let _ := (hG.topologicalAbelianization N).completedGroupAlgebraModule (G ⧸ N)
  have h : (⟨x ^ k * labuteComm x g, mul_mem (pow_mem hx k) (labuteComm_mem_of_mem_left hx g)⟩ :
      N) = (⟨x, hx⟩ : N) ^ k * ⟨labuteComm x g, labuteComm_mem_of_mem_left hx g⟩ :=
    Subtype.ext (by simp)
  rw [h, QuotientGroup.mk_mul, QuotientGroup.mk_pow, ofMul_mul, ofMul_pow,
    hG.ofMul_mk_labuteComm hx g, ← Nat.cast_smul_eq_nsmul (completedGroupAlgebra ℤ_[p] (G ⧸ N)),
    ← add_smul, ← add_sub_assoc, add_sub_right_comm]

/-- **The relator class of the `q ≠ 2` normal form.** For a tuple `x` whose entries
`x₁, …, x_{2m}` other than `x₂ = x 1` lie in `N`, `m = n / 2`, the class of
`x₁^q (x₁, x₂)(x₃, x₄) ⋯ (x_{2m-1}, x_{2m})` in `N^{ab}` is `(q - 1 + [x₂]⁻¹) • [x₁]` over
`ℤ_p[[G ⧸ N]]`. -/
theorem ofMul_mk_demushkinWordNeTwo (q : ℕ) {n : ℕ} (hn : 1 < n) {x : ℕ → G}
    (hx : ∀ i, i ≠ 1 → i < 2 * (n / 2) → x i ∈ N) :
    letI := (hG.topologicalAbelianization N).completedGroupAlgebraModule (G ⧸ N)
    Additive.ofMul ((⟨_, demushkinWordNeTwo_mem q n (pow_mem (hx 0 zero_ne_one (by omega)) q)
        fun i hi ↦ hx _ (by omega) (by omega)⟩ : N) : TopologicalAbelianization N) =
      ((q : completedGroupAlgebra ℤ_[p] (G ⧸ N)) - 1 +
          completedGroupAlgebra.of ℤ_[p] (G ⧸ N) (x 1 : G ⧸ N)⁻¹) •
        Additive.ofMul ((⟨x 0, hx 0 zero_ne_one (by omega)⟩ : N) :
          TopologicalAbelianization N) := by
  let _ := (hG.topologicalAbelianization N).completedGroupAlgebraModule (G ⧸ N)
  obtain ⟨m, hm⟩ : ∃ m, n / 2 = m + 1 := ⟨n / 2 - 1, by omega⟩
  have h0 : x 0 ∈ N := hx 0 zero_ne_one (by omega)
  -- The commutators after `(x₁, x₂)` pair elements of `N`, so their product lies in `⁅N, N⁆`.
  have ht : ((List.range m).map fun i ↦ labuteComm (x (2 * (i + 1))) (x (2 * (i + 1) + 1))).prod ∈
      ⁅N, N⁆ :=
    list_prod_map_labuteComm_range_mem_commutator m (fun i hi ↦ hx _ (by omega) (by omega))
      (fun i hi ↦ hx _ (by omega) (by omega))
  have h : (⟨_, demushkinWordNeTwo_mem q n (pow_mem h0 q) fun i hi ↦ hx _ (by omega) (by omega)⟩ :
      N) = ⟨x 0 ^ q * labuteComm (x 0) (x 1),
      mul_mem (pow_mem h0 q) (labuteComm_mem_of_mem_left h0 _)⟩ *
        ⟨_, Subgroup.commutator_le_left N N ht⟩ := by
    ext
    simp [demushkinWordNeTwo_def, hm, List.range_succ_eq_map, Function.comp_def, mul_assoc]
  rw [h, QuotientGroup.mk_mul, ofMul_mul, hG.ofMul_mk_pow_mul_labuteComm h0 (x 1) q,
    TopologicalAbelianization.ofMul_mk_eq_zero_of_mem_commutator _ ht, add_zero]

/-- **The relator class of the `q = 2`, `n` odd normal form.** For a tuple `x` with `x₁² ∈ N`
whose entries `x₁, …, x_{2m+1}` other than `x₁ = x 0` and `x₃ = x 2` lie in `N`, `m = n / 2`, the
class of `x₁² x₂^{2^f} (x₂, x₃)(x₄, x₅) ⋯ (x_{2m}, x_{2m+1})` in `N^{ab}` is
`[x₁²] + (2^f - 1 + [x₃]⁻¹) • [x₂]` over `ℤ_p[[G ⧸ N]]`. -/
theorem ofMul_mk_demushkinWordTwoOdd (f : ℕ) {n : ℕ} (hn : 1 < n) {x : ℕ → G}
    (hx₀ : x 0 ^ 2 ∈ N) (hx : ∀ i, i ≠ 0 → i ≠ 2 → i ≤ 2 * (n / 2) → x i ∈ N) :
    letI := (hG.topologicalAbelianization N).completedGroupAlgebraModule (G ⧸ N)
    Additive.ofMul ((⟨_, demushkinWordTwoOdd_mem f n hx₀
        (pow_mem (hx 1 one_ne_zero (by decide) (by omega)) _)
        fun i hi ↦ hx _ (by omega) (by omega) (by omega)⟩ : N) : TopologicalAbelianization N) =
      Additive.ofMul ((⟨x 0 ^ 2, hx₀⟩ : N) : TopologicalAbelianization N) +
        ((2 : completedGroupAlgebra ℤ_[p] (G ⧸ N)) ^ f - 1 +
            completedGroupAlgebra.of ℤ_[p] (G ⧸ N) (x 2 : G ⧸ N)⁻¹) •
          Additive.ofMul ((⟨x 1, hx 1 one_ne_zero (by decide) (by omega)⟩ : N) :
            TopologicalAbelianization N) := by
  let _ := (hG.topologicalAbelianization N).completedGroupAlgebraModule (G ⧸ N)
  obtain ⟨m, hm⟩ : ∃ m, n / 2 = m + 1 := ⟨n / 2 - 1, by omega⟩
  have h1 : x 1 ∈ N := hx 1 one_ne_zero (by decide) (by omega)
  -- The commutators after `(x₂, x₃)` pair elements of `N`, so their product lies in `⁅N, N⁆`.
  have ht : ((List.range m).map fun i ↦
      labuteComm (x (2 * (i + 1) + 1)) (x (2 * (i + 1) + 2))).prod ∈ ⁅N, N⁆ :=
    list_prod_map_labuteComm_range_mem_commutator m
      (fun i hi ↦ hx _ (by omega) (by omega) (by omega))
      (fun i hi ↦ hx _ (by omega) (by omega) (by omega))
  have h : (⟨_, demushkinWordTwoOdd_mem f n hx₀ (pow_mem h1 _)
      fun i hi ↦ hx _ (by omega) (by omega) (by omega)⟩ : N) =
      ⟨x 0 ^ 2, hx₀⟩ * (⟨x 1 ^ 2 ^ f * labuteComm (x 1) (x 2),
      mul_mem (pow_mem h1 _) (labuteComm_mem_of_mem_left h1 _)⟩ *
        ⟨_, Subgroup.commutator_le_left N N ht⟩) := by
    ext
    simp [demushkinWordTwoOdd_def, hm, List.range_succ_eq_map, Function.comp_def, mul_assoc]
  rw [h]
  simp only [QuotientGroup.mk_mul, ofMul_mul]
  rw [hG.ofMul_mk_pow_mul_labuteComm h1 (x 2),
    TopologicalAbelianization.ofMul_mk_eq_zero_of_mem_commutator _ ht, add_zero, Nat.cast_pow,
    Nat.cast_ofNat]

/-- **The relator class of the `q = 2`, `n` even normal form**, for `n ≥ 4`. For a tuple `x`
whose entries `x₁, …, x_{2m}` other than `x₂ = x 1` and `x₄ = x 3` lie in `N`, `m = n / 2`, the
class of `x₁^{2+a} (x₁, x₂) x₃^{2^f} (x₃, x₄) ⋯ (x_{2m-1}, x_{2m})` in `N^{ab}` is
`(1 + a + [x₂]⁻¹) • [x₁] + (2^f - 1 + [x₄]⁻¹) • [x₃]` over `ℤ_p[[G ⧸ N]]`. This is the expression
Labute computes on p. 122, up to the inversion of the acting group. -/
theorem ofMul_mk_demushkinWordTwoEven (a f : ℕ) {n : ℕ} (hn : 3 < n) {x : ℕ → G}
    (hx : ∀ i, i ≠ 1 → i ≠ 3 → i < 2 * (n / 2) → x i ∈ N) :
    letI := (hG.topologicalAbelianization N).completedGroupAlgebraModule (G ⧸ N)
    Additive.ofMul ((⟨_, demushkinWordTwoEven_mem a f n (hx 0 zero_ne_one (by decide) (by omega))
        (pow_mem (hx 2 (by decide) (by decide) (by omega)) _)
        fun i hi ↦ hx _ (by omega) (by omega) (by omega)⟩ : N) : TopologicalAbelianization N) =
      (1 + (a : completedGroupAlgebra ℤ_[p] (G ⧸ N)) +
            completedGroupAlgebra.of ℤ_[p] (G ⧸ N) (x 1 : G ⧸ N)⁻¹) •
          Additive.ofMul ((⟨x 0, hx 0 zero_ne_one (by decide) (by omega)⟩ : N) :
            TopologicalAbelianization N) +
        ((2 : completedGroupAlgebra ℤ_[p] (G ⧸ N)) ^ f - 1 +
            completedGroupAlgebra.of ℤ_[p] (G ⧸ N) (x 3 : G ⧸ N)⁻¹) •
          Additive.ofMul ((⟨x 2, hx 2 (by decide) (by decide) (by omega)⟩ : N) :
            TopologicalAbelianization N) := by
  let _ := (hG.topologicalAbelianization N).completedGroupAlgebraModule (G ⧸ N)
  obtain ⟨m, hm⟩ : ∃ m, n / 2 - 1 = m + 1 := ⟨n / 2 - 2, by omega⟩
  have h0 : x 0 ∈ N := hx 0 zero_ne_one (by decide) (by omega)
  have h2 : x 2 ∈ N := hx 2 (by decide) (by decide) (by omega)
  -- The commutators after `(x₃, x₄)` pair elements of `N`, so their product lies in `⁅N, N⁆`.
  have ht : ((List.range m).map fun i ↦
      labuteComm (x (2 * (i + 1) + 2)) (x (2 * (i + 1) + 3))).prod ∈ ⁅N, N⁆ :=
    list_prod_map_labuteComm_range_mem_commutator m
      (fun i hi ↦ hx _ (by omega) (by omega) (by omega))
      (fun i hi ↦ hx _ (by omega) (by omega) (by omega))
  have h : (⟨_, demushkinWordTwoEven_mem a f n h0 (pow_mem h2 _)
      fun i hi ↦ hx _ (by omega) (by omega) (by omega)⟩ : N) =
      ⟨x 0 ^ (2 + a) * labuteComm (x 0) (x 1),
        mul_mem (pow_mem h0 _) (labuteComm_mem_of_mem_left h0 _)⟩ *
        (⟨x 2 ^ 2 ^ f * labuteComm (x 2) (x 3),
          mul_mem (pow_mem h2 _) (labuteComm_mem_of_mem_left h2 _)⟩ *
            ⟨_, Subgroup.commutator_le_left N N ht⟩) := by
    ext
    simp [demushkinWordTwoEven_def, hm, List.range_succ_eq_map, Function.comp_def, mul_assoc]
  rw [h]
  simp only [QuotientGroup.mk_mul, ofMul_mul]
  rw [hG.ofMul_mk_pow_mul_labuteComm h0 (x 1), hG.ofMul_mk_pow_mul_labuteComm h2 (x 3),
    TopologicalAbelianization.ofMul_mk_eq_zero_of_mem_commutator _ ht, add_zero]
  congr 2 <;> norm_num [add_sub_right_comm]

/-- **The relator class of the `q = 2`, `n` even normal form**, for `n ≤ 3`, where the word is
`x₁^{2+a} (x₁, x₂) x₃^{2^f}`. For `x₁, x₃ ∈ N` the class in `N^{ab}` is
`(1 + a + [x₂]⁻¹) • [x₁] + 2^f • [x₃]` over `ℤ_p[[G ⧸ N]]`. On the generator tuples
`TauCeti.freeProPGen` and `TauCeti.presentedProPGen`, which are `1` out of range, `x₃ = 1` at
`n = 2` and the second term vanishes. -/
theorem ofMul_mk_demushkinWordTwoEven_of_le_three (a f : ℕ) {n : ℕ} (hn : n ≤ 3) {x : ℕ → G}
    (h0 : x 0 ∈ N) (h2 : x 2 ∈ N) :
    letI := (hG.topologicalAbelianization N).completedGroupAlgebraModule (G ⧸ N)
    Additive.ofMul ((⟨_, demushkinWordTwoEven_mem a f n h0 (pow_mem h2 _)
        fun i hi ↦ absurd hi (by omega)⟩ : N) : TopologicalAbelianization N) =
      (1 + (a : completedGroupAlgebra ℤ_[p] (G ⧸ N)) +
            completedGroupAlgebra.of ℤ_[p] (G ⧸ N) (x 1 : G ⧸ N)⁻¹) •
          Additive.ofMul ((⟨x 0, h0⟩ : N) : TopologicalAbelianization N) +
        ((2 : completedGroupAlgebra ℤ_[p] (G ⧸ N)) ^ f) •
          Additive.ofMul ((⟨x 2, h2⟩ : N) : TopologicalAbelianization N) := by
  let _ := (hG.topologicalAbelianization N).completedGroupAlgebraModule (G ⧸ N)
  have hm : n / 2 - 1 = 0 := by omega
  have h : (⟨_, demushkinWordTwoEven_mem a f n h0 (pow_mem h2 _)
      fun i hi ↦ absurd hi (by omega)⟩ : N) =
      ⟨x 0 ^ (2 + a) * labuteComm (x 0) (x 1),
        mul_mem (pow_mem h0 _) (labuteComm_mem_of_mem_left h0 _)⟩ * (⟨x 2, h2⟩ : N) ^ 2 ^ f := by
    ext
    simp [demushkinWordTwoEven_def, hm, mul_assoc]
  rw [h, QuotientGroup.mk_mul, QuotientGroup.mk_pow, ofMul_mul, ofMul_pow,
    hG.ofMul_mk_pow_mul_labuteComm h0 (x 1),
    ← Nat.cast_smul_eq_nsmul (completedGroupAlgebra ℤ_[p] (G ⧸ N))]
  congr 2 <;> norm_num [add_sub_right_comm]

/-! ### The relator classes in the abelianized kernel of a character -/

section Kernel

variable {A : Type*} [CommGroup A] [TopologicalSpace A] [T1Space A] (χ : G →ₜ* A)

/-- **The relator class of the `q ≠ 2` normal form in the abelianized kernel of a character.**
For a continuous character `χ` of a pro-`p` group `G` to a commutative `T1` group and a tuple `x`
with `χ (x i) = 1` for `i ≠ 1`, `i < 2 * (n / 2)`, the class of
`x₁^q (x₁, x₂)(x₃, x₄) ⋯ (x_{2m-1}, x_{2m})`, `m = n / 2`, in `X^{ab}`, `X = ker χ`, is
`(q - 1 + [x₂]⁻¹) • [x₁]` over `ℤ_p[[G ⧸ X]]`. For `G` free pro-`p` on `x₁, …, x_n` and `χ` the
standard orientation, `X^{ab}` is Labute's module `E`. -/
theorem ofMul_mk_demushkinWordNeTwo_ker (q : ℕ) {n : ℕ} (hn : 1 < n) {x : ℕ → G}
    (hx : ∀ i, i ≠ 1 → i < 2 * (n / 2) → χ (x i) = 1) :
    haveI := χ.isClosed_ker
    letI := (hG.topologicalAbelianization χ.toMonoidHom.ker).completedGroupAlgebraModule
      (G ⧸ χ.toMonoidHom.ker)
    Additive.ofMul ((⟨_, demushkinWordNeTwo_mem_ker χ.toMonoidHom q n
        ((congrArg (· ^ q) (hx 0 zero_ne_one (by omega))).trans (one_pow q))⟩ :
          χ.toMonoidHom.ker) :
          TopologicalAbelianization χ.toMonoidHom.ker) =
      ((q : completedGroupAlgebra ℤ_[p] (G ⧸ χ.toMonoidHom.ker)) - 1 +
          completedGroupAlgebra.of ℤ_[p] (G ⧸ χ.toMonoidHom.ker)
            (x 1 : G ⧸ χ.toMonoidHom.ker)⁻¹) •
        Additive.ofMul ((⟨x 0, MonoidHom.mem_ker.mpr (hx 0 zero_ne_one (by omega))⟩ :
          χ.toMonoidHom.ker) : TopologicalAbelianization χ.toMonoidHom.ker) :=
  haveI := χ.isClosed_ker
  hG.ofMul_mk_demushkinWordNeTwo q hn fun i hi hi' ↦ MonoidHom.mem_ker.mpr (hx i hi hi')

/-- **The relator class of the `q = 2`, `n` odd normal form in the abelianized kernel of a
character.** For a continuous character `χ` of a pro-`p` group `G` to a commutative `T1` group and
a tuple `x` with `χ (x 0) ^ 2 = 1` and `χ (x i) = 1` for `i ≠ 0, 2`, `i ≤ 2 * (n / 2)`, the
class of `x₁² x₂^{2^f} (x₂, x₃)(x₄, x₅) ⋯ (x_{2m}, x_{2m+1})`, `m = n / 2`, in `X^{ab}`,
`X = ker χ`, is `[x₁²] + (2^f - 1 + [x₃]⁻¹) • [x₂]` over `ℤ_p[[G ⧸ X]]`. -/
theorem ofMul_mk_demushkinWordTwoOdd_ker (f : ℕ) {n : ℕ} (hn : 1 < n) {x : ℕ → G}
    (hx₀ : χ (x 0) ^ 2 = 1) (hx : ∀ i, i ≠ 0 → i ≠ 2 → i ≤ 2 * (n / 2) → χ (x i) = 1) :
    haveI := χ.isClosed_ker
    letI := (hG.topologicalAbelianization χ.toMonoidHom.ker).completedGroupAlgebraModule
      (G ⧸ χ.toMonoidHom.ker)
    Additive.ofMul ((⟨_, demushkinWordTwoOdd_mem_ker χ.toMonoidHom f n hx₀
        ((congrArg (· ^ 2 ^ f) (hx 1 one_ne_zero (by decide) (by omega))).trans (one_pow _))⟩ :
          χ.toMonoidHom.ker) :
          TopologicalAbelianization χ.toMonoidHom.ker) =
      Additive.ofMul ((⟨x 0 ^ 2, MonoidHom.mem_ker.mpr ((map_pow χ.toMonoidHom _ _).trans hx₀)⟩ :
          χ.toMonoidHom.ker) : TopologicalAbelianization χ.toMonoidHom.ker) +
        ((2 : completedGroupAlgebra ℤ_[p] (G ⧸ χ.toMonoidHom.ker)) ^ f - 1 +
            completedGroupAlgebra.of ℤ_[p] (G ⧸ χ.toMonoidHom.ker)
              (x 2 : G ⧸ χ.toMonoidHom.ker)⁻¹) •
          Additive.ofMul ((⟨x 1, MonoidHom.mem_ker.mpr (hx 1 one_ne_zero (by decide) (by omega))⟩ :
            χ.toMonoidHom.ker) : TopologicalAbelianization χ.toMonoidHom.ker) :=
  haveI := χ.isClosed_ker
  hG.ofMul_mk_demushkinWordTwoOdd f hn _ fun i hi₀ hi₂ hi ↦
    MonoidHom.mem_ker.mpr (hx i hi₀ hi₂ hi)

/-- **The relator class of the `q = 2`, `n` even normal form in the abelianized kernel of a
character**, for `n ≥ 4`. For a continuous character `χ` of a pro-`p` group `G` to a commutative
`T1` group and a tuple `x` with `χ (x i) = 1` for `i ≠ 1, 3`, `i < 2 * (n / 2)`, the class of
`x₁^{2+a} (x₁, x₂) x₃^{2^f} (x₃, x₄) ⋯ (x_{2m-1}, x_{2m})`, `m = n / 2`, in `X^{ab}`,
`X = ker χ`, is
`(1 + a + [x₂]⁻¹) • [x₁] + (2^f - 1 + [x₄]⁻¹) • [x₃]` over `ℤ_p[[G ⧸ X]]`. For `G` free pro-`2` on
`x₁, …, x_n` and `χ` the standard orientation, this is the expression of Labute, p. 122, up to
the inversion of the acting group. -/
theorem ofMul_mk_demushkinWordTwoEven_ker (a f : ℕ) {n : ℕ} (hn : 3 < n) {x : ℕ → G}
    (hx : ∀ i, i ≠ 1 → i ≠ 3 → i < 2 * (n / 2) → χ (x i) = 1) :
    haveI := χ.isClosed_ker
    letI := (hG.topologicalAbelianization χ.toMonoidHom.ker).completedGroupAlgebraModule
      (G ⧸ χ.toMonoidHom.ker)
    Additive.ofMul ((⟨_, demushkinWordTwoEven_mem_ker χ.toMonoidHom a f n
        ((congrArg (· ^ (2 + a)) (hx 0 zero_ne_one (by decide) (by omega))).trans (one_pow _))
        ((congrArg (· ^ 2 ^ f) (hx 2 (by decide) (by decide) (by omega))).trans (one_pow _))⟩ :
          χ.toMonoidHom.ker) :
          TopologicalAbelianization χ.toMonoidHom.ker) =
      (1 + (a : completedGroupAlgebra ℤ_[p] (G ⧸ χ.toMonoidHom.ker)) +
            completedGroupAlgebra.of ℤ_[p] (G ⧸ χ.toMonoidHom.ker)
              (x 1 : G ⧸ χ.toMonoidHom.ker)⁻¹) •
          Additive.ofMul ((⟨x 0, MonoidHom.mem_ker.mpr (hx 0 zero_ne_one (by decide) (by omega))⟩ :
            χ.toMonoidHom.ker) : TopologicalAbelianization χ.toMonoidHom.ker) +
        ((2 : completedGroupAlgebra ℤ_[p] (G ⧸ χ.toMonoidHom.ker)) ^ f - 1 +
            completedGroupAlgebra.of ℤ_[p] (G ⧸ χ.toMonoidHom.ker)
              (x 3 : G ⧸ χ.toMonoidHom.ker)⁻¹) •
          Additive.ofMul ((⟨x 2, MonoidHom.mem_ker.mpr
            (hx 2 (by decide) (by decide) (by omega))⟩ : χ.toMonoidHom.ker) :
              TopologicalAbelianization χ.toMonoidHom.ker) :=
  haveI := χ.isClosed_ker
  hG.ofMul_mk_demushkinWordTwoEven a f hn fun i hi₁ hi₃ hi ↦
    MonoidHom.mem_ker.mpr (hx i hi₁ hi₃ hi)

/-- **The relator class of the `q = 2`, `n` even normal form in the abelianized kernel of a
character**, for `n ≤ 3`, where the word is `x₁^{2+a} (x₁, x₂) x₃^{2^f}`. For a continuous
character `χ` of a pro-`p` group `G` to a commutative `T1` group and a tuple `x` with
`χ (x 0) = 1` and `χ (x 2) = 1`, the class in `X^{ab}`, `X = ker χ`, is
`(1 + a + [x₂]⁻¹) • [x₁] + 2^f • [x₃]` over `ℤ_p[[G ⧸ X]]`. On the generator tuples
`TauCeti.freeProPGen` and `TauCeti.presentedProPGen`, which are `1` out of range, `x₃ = 1` at
`n = 2` and the second term vanishes. -/
theorem ofMul_mk_demushkinWordTwoEven_ker_of_le_three (a f : ℕ) {n : ℕ} (hn : n ≤ 3) {x : ℕ → G}
    (h0 : χ (x 0) = 1) (h2 : χ (x 2) = 1) :
    haveI := χ.isClosed_ker
    letI := (hG.topologicalAbelianization χ.toMonoidHom.ker).completedGroupAlgebraModule
      (G ⧸ χ.toMonoidHom.ker)
    Additive.ofMul ((⟨_, demushkinWordTwoEven_mem_ker χ.toMonoidHom a f n
        ((congrArg (· ^ (2 + a)) h0).trans (one_pow _))
        ((congrArg (· ^ 2 ^ f) h2).trans (one_pow _))⟩ : χ.toMonoidHom.ker) :
          TopologicalAbelianization χ.toMonoidHom.ker) =
      (1 + (a : completedGroupAlgebra ℤ_[p] (G ⧸ χ.toMonoidHom.ker)) +
            completedGroupAlgebra.of ℤ_[p] (G ⧸ χ.toMonoidHom.ker)
              (x 1 : G ⧸ χ.toMonoidHom.ker)⁻¹) •
          Additive.ofMul ((⟨x 0, MonoidHom.mem_ker.mpr h0⟩ : χ.toMonoidHom.ker) :
            TopologicalAbelianization χ.toMonoidHom.ker) +
        ((2 : completedGroupAlgebra ℤ_[p] (G ⧸ χ.toMonoidHom.ker)) ^ f) •
          Additive.ofMul ((⟨x 2, MonoidHom.mem_ker.mpr h2⟩ : χ.toMonoidHom.ker) :
            TopologicalAbelianization χ.toMonoidHom.ker) :=
  haveI := χ.isClosed_ker
  hG.ofMul_mk_demushkinWordTwoEven_of_le_three a f hn _ _

end Kernel

end Module

end IsProP

end TauCeti
