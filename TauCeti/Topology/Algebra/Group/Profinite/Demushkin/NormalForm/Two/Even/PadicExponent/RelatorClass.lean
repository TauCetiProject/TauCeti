/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.NormalForm.RelatorClass
public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.NormalForm.Two.Even.PadicExponent.Basic

/-!
# The class of the dyadic relator with a `2`-adic exponent

For a closed normal subgroup `N` of a pro-`2` group `G`, write `E = N^{ab}` and
`Λ = ℤ₂[[G ⧸ N]]`, acting by conjugation. If the unmarked generators lie in `N`, the
class of `x₁^{2+α} (x₁,x₂) x₃^q (x₃,x₄) ⋯` in `E` is

`(1 + α + [x₂]⁻¹) • [x₁] + (q - 1 + [x₄]⁻¹) • [x₃]`.

Here `α` is any `2`-adic integer, including exponents that are not natural numbers;
`q = 0` includes the infinite-level endpoint. For ranks at most three there is no
commutator `(x₃,x₄)`, and the second coefficient is simply `q`. At rank two on a tuple
with `x₃ = 1`, that term vanishes. These formulas allow coefficient division in the
completed group algebra to be applied to the actual `2`-adic relator.

The calculation extends the natural-exponent calculation in
`TauCeti.Topology.Algebra.Group.Profinite.Demushkin.NormalForm.RelatorClass`, reusing its
commutator formula and the calculation for the tail. Labute uses the inverse conjugation
action, so his coefficients contain `[x₂]` and `[x₄]` where ours contain their inverses.

## References

* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967),
  Section 4, pp. 121–122.
-/

public section

namespace TauCeti.IsProP

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G] (hG : IsProP 2 G)
  {N : Subgroup G} [N.Normal] [IsClosed (N : Set G)]

include hG

/-- The class of the even dyadic relator with an arbitrary `2`-adic exponent, in the
abelianization of a closed normal subgroup containing the unmarked generators. -/
theorem ofMul_mk_demushkinWordTwoEvenPadic (α : ℤ_[2]) (q : ℕ) {n : ℕ} (hn : 3 < n)
    {x : ℕ → G} (hx : ∀ i, i ≠ 1 → i ≠ 3 → i < 2 * (n / 2) → x i ∈ N) :
    letI := (hG.topologicalAbelianization N).completedGroupAlgebraModule (G ⧸ N)
    Additive.ofMul ((⟨_, demushkinWordTwoEvenPadic_mem hG α q n x
        ‹IsClosed (N : Set G)› (hx 0 (by decide) (by decide) (by omega))
        (pow_mem (hx 2 (by decide) (by decide) (by omega)) q)
        (fun i hi ↦ hx _ (by omega) (by omega) (by omega))⟩ : N) :
          TopologicalAbelianization N) =
      (1 + algebraMap ℤ_[2] (completedGroupAlgebra ℤ_[2] (G ⧸ N)) α +
          completedGroupAlgebra.of ℤ_[2] (G ⧸ N) (x 1 : G ⧸ N)⁻¹) •
        Additive.ofMul ((⟨x 0, hx 0 (by decide) (by decide) (by omega)⟩ : N) :
          TopologicalAbelianization N) +
      ((q : completedGroupAlgebra ℤ_[2] (G ⧸ N)) - 1 +
          completedGroupAlgebra.of ℤ_[2] (G ⧸ N) (x 3 : G ⧸ N)⁻¹) •
        Additive.ofMul ((⟨x 2, hx 2 (by decide) (by decide) (by omega)⟩ : N) :
          TopologicalAbelianization N) := by
  let _ := (hG.topologicalAbelianization N).completedGroupAlgebraModule (G ⧸ N)
  have h0 := hx 0 (by decide) (by decide) (by omega)
  have ht : ∀ i, i ≠ 1 → i < 2 * ((n - 2) / 2) → x (i + 2) ∈ N :=
    fun i hi hn ↦ hx _ (by omega) (by omega) (by omega)
  have hr := demushkinWordTwoEvenPadic_mem hG α q n x
    ‹IsClosed (N : Set G)› h0 (pow_mem (ht 0 (by decide) (by omega)) q)
    (fun i hi ↦ hx _ (by omega) (by omega) (by omega))
  have hsplit : (⟨demushkinWordTwoEvenPadic hG α q n x, hr⟩ : N) =
      ⟨hG.padicPow (x 0) (2 + α) * labuteComm (x 0) (x 1),
        mul_mem (hG.padicPow_mem ‹IsClosed (N : Set G)› h0 _)
          (labuteComm_mem_of_mem_left h0 _)⟩ *
      ⟨demushkinWordNeTwo q (n - 2) (fun i ↦ x (i + 2)),
        demushkinWordNeTwo_mem q (n - 2) (pow_mem (ht 0 (by decide) (by omega)) q)
          (fun i hi ↦ ht _ (by omega) (by omega))⟩ :=
    Subtype.ext (demushkinWordTwoEvenPadic_eq_padicPow_mul_labuteComm_mul
      hG α q n x (by omega))
  rw [hsplit, QuotientGroup.mk_mul, ofMul_mul,
    hG.ofMul_mk_padicPow_mul_labuteComm h0,
    hG.ofMul_mk_demushkinWordNeTwo q (by omega) ht]
  congr 2
  simp only [map_add, map_ofNat]
  norm_num [add_sub_right_comm]

/-- At ranks at most three, the class of the even dyadic word is the sum of the
first marked contribution and `q` times the class of its third entry. -/
theorem ofMul_mk_demushkinWordTwoEvenPadic_of_le_three (α : ℤ_[2]) (q : ℕ) {n : ℕ}
    (hn : n ≤ 3) {x : ℕ → G} (h0 : x 0 ∈ N) (h2 : x 2 ∈ N) :
    letI := (hG.topologicalAbelianization N).completedGroupAlgebraModule (G ⧸ N)
    Additive.ofMul ((⟨_, demushkinWordTwoEvenPadic_mem hG α q n x
        ‹IsClosed (N : Set G)› h0 (pow_mem h2 q) (fun i hi ↦ absurd hi (by omega))⟩ : N) :
          TopologicalAbelianization N) =
      (1 + algebraMap ℤ_[2] (completedGroupAlgebra ℤ_[2] (G ⧸ N)) α +
          completedGroupAlgebra.of ℤ_[2] (G ⧸ N) (x 1 : G ⧸ N)⁻¹) •
        Additive.ofMul ((⟨x 0, h0⟩ : N) : TopologicalAbelianization N) +
      (q : completedGroupAlgebra ℤ_[2] (G ⧸ N)) •
        Additive.ofMul ((⟨x 2, h2⟩ : N) : TopologicalAbelianization N) := by
  let _ := (hG.topologicalAbelianization N).completedGroupAlgebraModule (G ⧸ N)
  have hm : n / 2 - 1 = 0 := by omega
  have hr := demushkinWordTwoEvenPadic_mem hG α q n x
    ‹IsClosed (N : Set G)› h0 (pow_mem h2 q) (fun i hi ↦ absurd hi (by omega))
  have hsplit : (⟨demushkinWordTwoEvenPadic hG α q n x, hr⟩ : N) =
      ⟨hG.padicPow (x 0) (2 + α) * labuteComm (x 0) (x 1),
        mul_mem (hG.padicPow_mem ‹IsClosed (N : Set G)› h0 _)
          (labuteComm_mem_of_mem_left h0 _)⟩ * (⟨x 2, h2⟩ : N) ^ q := by
    ext
    simp [demushkinWordTwoEvenPadic_def, hm]
  rw [hsplit, QuotientGroup.mk_mul, QuotientGroup.mk_pow, ofMul_mul, ofMul_pow,
    hG.ofMul_mk_padicPow_mul_labuteComm h0,
    ← Nat.cast_smul_eq_nsmul (completedGroupAlgebra ℤ_[2] (G ⧸ N))]
  congr 2
  simp only [map_add, map_ofNat]
  norm_num [add_sub_right_comm]

end TauCeti.IsProP
