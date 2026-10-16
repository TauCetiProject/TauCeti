/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.TwistedUnits
public import TauCeti.Topology.Algebra.Group.Profinite.CompletedGroupAlgebra.CharacterDivision
public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.NormalForm.RelatorClass

/-!
# Factoring a dyadic normal-form relator by a prescribed orientation generator

Let `χ : G → ℤ₂ˣ` be a continuous character of a pro-`2` group and `E = (ker χ)^{ab}`,
with the completed conjugation action of `Λ = ℤ₂[[G / ker χ]]`. For a dyadic even-rank
normal-form word, its class in `E` is a sum of two terms with coefficients
`1 + a + [x₂]⁻¹` and `2^g - 1 + [x₄]⁻¹`. When the marked character values satisfy
`χ(x₂)(1 + a) = -1` and `χ(x₄)(1 - 2^g) = 1`, both coefficients vanish along the character.

If `χ(y)` generates the image of `χ` topologically and has value `-b`, both coefficients
are divisible by `b + [y]`. Consequently the relator class is `(b + [y]) • z` for some
`z ∈ E`. Taking `b = 1 + 2^f` gives the multiplier in Labute's Theorem 5 for the branch
with procyclic orientation image. The tuple need not generate `G`, and the argument needs
neither freeness nor a Demushkin hypothesis.

We use the conjugation convention `[y] • [x] = [y x y⁻¹]`. Labute uses inverse conjugation;
his generator in the power-series coordinate is therefore the inverse of the one used here.

## References

* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), §4.1,
  pp. 122–123, Theorem 5.
-/

public section

namespace TauCeti.IsProP

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G] (hG : IsProP 2 G) (χ : G →ₜ* ℤ_[2]ˣ)
include hG

/-- The class of the dyadic even-rank normal-form word is divisible, in the abelianized
character kernel, by the coefficient attached to any topological generator of the character
image. For `b = 1 + 2^f` this is the normal-form factorization in Labute's Theorem 5. -/
theorem exists_ofMul_mk_demushkinWordTwoEven_ker_eq_smul_of_range (a g : ℕ) {n : ℕ}
    (hn : 3 < n) {x : ℕ → G}
    (hx : ∀ i, i ≠ 1 → i ≠ 3 → i < 2 * (n / 2) → χ (x i) = 1)
    (h₁ : (χ (x 1) : ℤ_[2]) * (1 + a) = -1)
    (h₃ : (χ (x 3) : ℤ_[2]) * (1 - 2 ^ g) = 1)
    (y : G) (hrange : χ.toMonoidHom.range = (Subgroup.closure {χ y}).topologicalClosure)
    {b : ℤ_[2]} (hy : (χ y : ℤ_[2]) = -b) :
    haveI := χ.isClosed_ker
    letI := (hG.topologicalAbelianization χ.toMonoidHom.ker).completedGroupAlgebraModule
      (G ⧸ χ.toMonoidHom.ker)
    ∃ z : Additive (TopologicalAbelianization χ.toMonoidHom.ker),
      Additive.ofMul ((⟨_, demushkinWordTwoEven_mem_ker χ.toMonoidHom a g n
          ((congrArg (· ^ (2 + a)) (hx 0 zero_ne_one (by decide) (by omega))).trans (one_pow _))
          ((congrArg (· ^ 2 ^ g) (hx 2 (by decide) (by decide) (by omega))).trans (one_pow _))⟩ :
            χ.toMonoidHom.ker) : TopologicalAbelianization χ.toMonoidHom.ker) =
        (algebraMap ℤ_[2] (completedGroupAlgebra ℤ_[2] (G ⧸ χ.toMonoidHom.ker)) b +
          completedGroupAlgebra.of ℤ_[2] (G ⧸ χ.toMonoidHom.ker)
            (y : G ⧸ χ.toMonoidHom.ker)) • z := by
  have := χ.isClosed_ker
  let _ := (hG.topologicalAbelianization χ.toMonoidHom.ker).completedGroupAlgebraModule
    (G ⧸ χ.toMonoidHom.ker)
  have hinv₁ : (((χ (x 1))⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) = -(1 + a) :=
    Units.inv_eq_of_mul_eq_one_right (by rw [mul_neg, h₁, neg_neg])
  have hinv₃ : (((χ (x 3))⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) = -((2 : ℤ_[2]) ^ g - 1) := by
    rw [Units.inv_eq_of_mul_eq_one_right h₃]
    ring
  have hdiv (t : G) (s : ℤ_[2]) (hs : (χ t : ℤ_[2]) = -s) :
      algebraMap ℤ_[2] (completedGroupAlgebra ℤ_[2] (G ⧸ χ.toMonoidHom.ker)) b +
          completedGroupAlgebra.of ℤ_[2] (G ⧸ χ.toMonoidHom.ker) (y : G ⧸ χ.toMonoidHom.ker) ∣
        algebraMap ℤ_[2] (completedGroupAlgebra ℤ_[2] (G ⧸ χ.toMonoidHom.ker)) s +
          completedGroupAlgebra.of ℤ_[2] (G ⧸ χ.toMonoidHom.ker) (t : G ⧸ χ.toMonoidHom.ker) := by
    have hd := hG.of_sub_algebraMap_dvd_algebraMap_add_of_range χ y hrange t hs
    simpa only [hy, map_neg, sub_neg_eq_add, add_comm] using hd
  obtain ⟨c₁, hc₁⟩ := hdiv (x 1)⁻¹ (1 + a) (by simpa only [map_inv] using hinv₁)
  obtain ⟨c₃, hc₃⟩ := hdiv (x 3)⁻¹ (2 ^ g - 1) (by simpa only [map_inv] using hinv₃)
  refine ⟨c₁ • Additive.ofMul ((⟨x 0, MonoidHom.mem_ker.mpr
    (hx 0 zero_ne_one (by decide) (by omega))⟩ : χ.toMonoidHom.ker) :
      TopologicalAbelianization χ.toMonoidHom.ker) +
    c₃ • Additive.ofMul ((⟨x 2, MonoidHom.mem_ker.mpr
      (hx 2 (by decide) (by decide) (by omega))⟩ : χ.toMonoidHom.ker) :
        TopologicalAbelianization χ.toMonoidHom.ker), ?_⟩
  simp only [QuotientGroup.mk_inv] at hc₁ hc₃
  rw [hG.ofMul_mk_demushkinWordTwoEven_ker χ a g hn hx, smul_add, ← mul_smul, ← mul_smul,
    ← hc₁, ← hc₃]
  simp only [map_add, map_sub, map_pow, map_natCast, map_ofNat, map_one]

/-- The normal-form case of Labute's Theorem 5, with the prescribed multiplier
`(1 + 2^f) + [y]` and the orientation image `U^[f]`. The image equation guarantees that every
`y` with character value `-(1 + 2^f)` is a topological generator modulo the character kernel. -/
theorem exists_ofMul_mk_demushkinWordTwoEven_ker_eq_smul_of_range_eq_procyclicClosure
    (a g : ℕ) {n : ℕ} (hn : 3 < n) {x : ℕ → G}
    (hx : ∀ i, i ≠ 1 → i ≠ 3 → i < 2 * (n / 2) → χ (x i) = 1)
    (h₁ : (χ (x 1) : ℤ_[2]) * (1 + a) = -1)
    (h₃ : (χ (x 3) : ℤ_[2]) * (1 - 2 ^ g) = 1)
    {f : ℕ} (hf : 2 ≤ f) {u : ℤ_[2]ˣ} (hu : (u : ℤ_[2]) = -1 + 2 ^ f)
    (hrange : χ.toMonoidHom.range = (Subgroup.zpowers u).topologicalClosure)
    (y : G) (hy : (χ y : ℤ_[2]) = -(1 + 2 ^ f)) :
    haveI := χ.isClosed_ker
    letI := (hG.topologicalAbelianization χ.toMonoidHom.ker).completedGroupAlgebraModule
      (G ⧸ χ.toMonoidHom.ker)
    ∃ z : Additive (TopologicalAbelianization χ.toMonoidHom.ker),
      Additive.ofMul ((⟨_, demushkinWordTwoEven_mem_ker χ.toMonoidHom a g n
          ((congrArg (· ^ (2 + a)) (hx 0 zero_ne_one (by decide) (by omega))).trans (one_pow _))
          ((congrArg (· ^ 2 ^ g) (hx 2 (by decide) (by decide) (by omega))).trans (one_pow _))⟩ :
            χ.toMonoidHom.ker) : TopologicalAbelianization χ.toMonoidHom.ker) =
        (algebraMap ℤ_[2] (completedGroupAlgebra ℤ_[2] (G ⧸ χ.toMonoidHom.ker)) (1 + 2 ^ f) +
          completedGroupAlgebra.of ℤ_[2] (G ⧸ χ.toMonoidHom.ker)
            (y : G ⧸ χ.toMonoidHom.ker)) • z := by
  have hv : ((-(χ y) : ℤ_[2]ˣ) : ℤ_[2]) - 1 = 2 ^ f := by
    rw [Units.val_neg, hy]
    ring
  have hv₀ : -(χ y) ∈ unitsPrincipal 2 f := by
    rw [mem_unitsPrincipal_iff, hv, Nat.cast_ofNat]
  have hv₁ : -(χ y) ∉ unitsPrincipal 2 (f + 1) := by
    rw [mem_unitsPrincipal_iff, hv, Nat.cast_ofNat,
      pow_dvd_pow_iff (by norm_num : (2 : ℤ_[2]) ≠ 0) PadicInt.p_nonunit]
    omega
  have hgen : χ.toMonoidHom.range = (Subgroup.closure {χ y}).topologicalClosure := by
    rw [hrange, ← Subgroup.zpowers_eq_closure]
    exact (topologicalClosure_zpowers_two_eq_iff hf hf
      (neg_mem_unitsPrincipal_two_of_val_eq hu) (neg_notMem_unitsPrincipal_two_succ_of_val_eq hu)
      hv₀ hv₁).mpr rfl
  exact hG.exists_ofMul_mk_demushkinWordTwoEven_ker_eq_smul_of_range χ a g hn hx h₁ h₃ y hgen hy

end TauCeti.IsProP
