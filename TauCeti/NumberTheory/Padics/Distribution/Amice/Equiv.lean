/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.Bases.Orthonormal
public import TauCeti.NumberTheory.Padics.Distribution.Amice.Basis
public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Triangular

/-!
# Amice's theorem: the analytic basis of `LA_h`

For `h, n : ℕ` put `m_h(n) = ⌊n / pʰ⌋!` and `e_{h,n}(x) = m_h(n) (x choose n)`. Amice's theorem
asserts that the disc expansions of these polynomials are an orthonormal basis of the analytic
stage `LA_h(ℤ_p)` (`TauCeti.AnalyticStage.isOrthonormalBasis_amiceTerm`). More generally, for
every complete ultrametric normed `ℤ_p`-module `E` with contractive action, Amice's map

`TauCeti.AnalyticStage.amiceMap p h S : C₀(ℕ, E) → LA_h(E) = C₀(ZMod (pʰ) × ℕ, E)`,
`(cₙ) ↦ ∑ₙ e_{h,n} • cₙ`,

is an isometric isomorphism (`TauCeti.AnalyticStage.amiceEquiv`). No torsion-freeness of `E` is
needed: the statement concerns coefficient vectors, not the functions they evaluate to.

The proof is the triangularity argument of Colmez. Write `N = pʰ`. Match the Amice index `n` with
the coordinate `(n mod N, ⌊n / N⌋)` of `LA_h`, and order these coordinates by their degree
`⌊n / N⌋` and then by *decreasing* centre `n mod N`. In the natural numbers this ordering is the
reversal `l ↦ N ⌊l / N⌋ + (N - 1 - l mod N)` of each block `[N q, N q + N)`. In these
coordinates the matrix of Amice's map has

* integral entries, by the integrality of Amice's polynomials on discs;
* unit diagonal entries: the coefficient of `w ^ ⌊n / N⌋` on the disc of `n mod N`
  (`TauCeti.norm_coeff_amicePolynomial_mod_div`);
* entries in `pℤ_p` below the diagonal: modulo `p`, Amice's polynomial has degree at most
  `⌊n / N⌋` on every disc (`TauCeti.norm_coeff_amicePolynomial_lt_one_of_div_lt`) and vanishes on
  the discs of the centres `a < n mod N` (`TauCeti.norm_coeff_amicePolynomial_lt_one_of_mod_lt`);
* finite columns.

Such a matrix defines an isometric automorphism of `C₀(ℕ, E)`
(`Matrix.toZeroAtInftySMulLinearIsometryEquiv`).

## Main definitions

* `TauCeti.AnalyticStage.amiceEquiv p h S`: Amice's isometric isomorphism
  `C₀(ℕ, E) ≃ₗᵢ[S] LA_h(E)`.

## Main results

* `TauCeti.AnalyticStage.norm_amiceMap`: Amice's map preserves norms.
* `TauCeti.AnalyticStage.amiceMap_surjective`: Amice's map is onto.
* `TauCeti.AnalyticStage.amiceEquiv_symm_amiceTerm`: the inverse of Amice's isomorphism sends
  Amice's vector `e_{h,n} • e` to the coordinate vector `single n e`.
* `TauCeti.AnalyticStage.isOrthonormalBasis_amiceTerm`: Amice's basis theorem for `LA_h(ℤ_p)`.

## References

* Y. Amice, *Interpolation p-adique*, Bull. Soc. Math. France 92 (1964), 117–180.
* P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010), §I.4.
-/

public section

open Filter Topology Polynomial
open scoped ZeroAtInfty

variable {p : ℕ} [hp : Fact p.Prime]

namespace TauCeti

namespace AnalyticStage

/-! ### The reindexing -/

section Index

variable (p) in
/-- The reversal `l ↦ pʰ ⌊l / pʰ⌋ + (pʰ - 1 - l mod pʰ)` of each block `[pʰ q, pʰ q + pʰ)` of
natural numbers. -/
private def amiceIndex (h l : ℕ) : ℕ := p ^ h * (l / p ^ h) + (p ^ h - 1 - l % p ^ h)

private theorem amiceIndex_div (h l : ℕ) : amiceIndex p h l / p ^ h = l / p ^ h := by
  have hN : 0 < p ^ h := pow_pos hp.out.pos h
  rw [amiceIndex, Nat.mul_add_div hN, Nat.div_eq_of_lt (a := p ^ h - 1 - l % p ^ h)
    ((Nat.sub_le _ _).trans_lt (Nat.sub_lt hN Nat.one_pos)), add_zero]

private theorem amiceIndex_mod (h l : ℕ) :
    amiceIndex p h l % p ^ h = p ^ h - 1 - l % p ^ h := by
  have hN : 0 < p ^ h := pow_pos hp.out.pos h
  rw [amiceIndex, Nat.mul_add_mod,
    Nat.mod_eq_of_lt ((Nat.sub_le _ _).trans_lt (Nat.sub_lt hN Nat.one_pos))]

private theorem amiceIndex_involutive (h : ℕ) : Function.Involutive (amiceIndex p h) := fun l ↦ by
  have hlt := Nat.mod_lt l (pow_pos hp.out.pos h)
  have hl := Nat.div_add_mod l (p ^ h)
  rw [amiceIndex, amiceIndex_div h l, amiceIndex_mod h l]
  generalize l / p ^ h = q at *
  generalize l % p ^ h = r at *
  omega

variable (p) in
/-- The coordinate of `LA_h` matched with the `k`-th natural number in the triangular ordering:
the centre `amiceIndex p h k mod pʰ` and the degree `⌊k / pʰ⌋`. -/
private def amiceCoord (h : ℕ) : ℕ ≃ ZMod (p ^ h) × ℕ where
  toFun k := ((amiceIndex p h k : ZMod (p ^ h)), k / p ^ h)
  invFun i := p ^ h * i.2 + (p ^ h - 1 - i.1.val)
  left_inv k := by
    have hlt := Nat.mod_lt k (pow_pos hp.out.pos h)
    have hk := Nat.div_add_mod k (p ^ h)
    simp only [ZMod.val_natCast, amiceIndex_mod h k]
    generalize k / p ^ h = q at *
    generalize k % p ^ h = r at *
    omega
  right_inv i := by
    have hN : 0 < p ^ h := pow_pos hp.out.pos h
    have : NeZero (p ^ h) := ⟨hN.ne'⟩
    have hval := ZMod.val_lt i.1
    have hdiv : (p ^ h * i.2 + (p ^ h - 1 - i.1.val)) / p ^ h = i.2 := by
      rw [Nat.mul_add_div hN, Nat.div_eq_of_lt (a := p ^ h - 1 - i.1.val) (by omega), add_zero]
    have hmod : (p ^ h * i.2 + (p ^ h - 1 - i.1.val)) % p ^ h = p ^ h - 1 - i.1.val := by
      rw [Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
    refine Prod.ext ?_ hdiv
    dsimp only
    rw [amiceIndex, hdiv, hmod, Nat.sub_sub_self (by omega), Nat.cast_add, Nat.cast_mul,
      ZMod.natCast_self, zero_mul, zero_add, ZMod.natCast_zmod_val]

variable (p) in
/-- The block reversal `amiceIndex` as a permutation of `ℕ`; it is its own inverse. -/
private def amicePerm (h : ℕ) : Equiv.Perm ℕ := (amiceIndex_involutive (p := p) h).toPerm _

private theorem val_amiceCoord_fst (h k : ℕ) :
    (amiceCoord p h k).1.val = amiceIndex p h k % p ^ h :=
  ZMod.val_natCast _ _

private theorem amiceCoord_snd (h k : ℕ) : (amiceCoord p h k).2 = k / p ^ h := (rfl)

end Index

/-! ### The matrix of Amice's map -/

section Matrix

variable (p) in
/-- The matrix of Amice's map in the triangular ordering: its column `l` is the expansion of
`e_{h,n}` with `n = amiceIndex p h l`, and its row `k` is the coordinate `amiceCoord p h k`. -/
private noncomputable def amiceMatrix (h : ℕ) : Matrix ℕ ℕ ℤ_[p] := fun k l ↦
  (amicePolynomial p h (amiceIndex p h l) (amiceIndex p h k % p ^ h : ℕ)).coeff (k / p ^ h)

private theorem amiceMatrix_eq (h k l : ℕ) :
    amiceMatrix p h k l = (amicePolynomial p h (amiceIndex p h l)
      ((amiceCoord p h k).1.val : ℤ_[p])).coeff (amiceCoord p h k).2 := by
  rw [val_amiceCoord_fst, amiceCoord_snd, amiceMatrix]

private theorem tendsto_amiceMatrix (h l : ℕ) :
    Tendsto (fun k ↦ amiceMatrix p h k l) cofinite (𝓝 0) := by
  have hN : 0 < p ^ h := pow_pos hp.out.pos h
  refine tendsto_nhds_of_eventually_eq ?_
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [eventually_ge_atTop (p ^ h * (amiceIndex p h l + 1))] with k hk
  refine coeff_amicePolynomial_eq_zero _ ?_
  rw [Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le hN, mul_comm]
  exact hk

private theorem norm_amiceMatrix_le (h k l : ℕ) : ‖amiceMatrix p h k l‖ ≤ 1 :=
  PadicInt.norm_le_one _

private theorem norm_amiceMatrix_self (h k : ℕ) : ‖amiceMatrix p h k k‖ = 1 := by
  rw [amiceMatrix, ← amiceIndex_div h k]
  exact norm_coeff_amicePolynomial_mod_div h _

private theorem norm_amiceMatrix_le_of_lt (h : ℕ) {k l : ℕ} (hlk : l < k) :
    ‖amiceMatrix p h k l‖ ≤ (p : ℝ) ^ (-1 : ℤ) := by
  have hN : 0 < p ^ h := pow_pos hp.out.pos h
  rw [PadicInt.norm_le_pow_iff_norm_lt_pow_add_one, neg_add_cancel, zpow_zero]
  rcases (Nat.div_le_div_right (c := p ^ h) hlk.le).lt_or_eq with hdiv | hdiv
  · -- A higher degree: modulo `p`, the column has degree at most `⌊n / pʰ⌋`.
    refine norm_coeff_amicePolynomial_lt_one_of_div_lt _ ?_
    rwa [amiceIndex_div h l]
  · -- The same degree and a smaller centre: modulo `p`, the column vanishes on that disc.
    refine norm_coeff_amicePolynomial_lt_one_of_mod_lt ?_ _
    have hl := Nat.div_add_mod l (p ^ h)
    have hk := Nat.div_add_mod k (p ^ h)
    have := Nat.mod_lt k hN
    rw [Nat.mod_mod, amiceIndex_mod h k, amiceIndex_mod h l]
    rw [hdiv] at hl
    generalize k / p ^ h = q at *
    omega

/-- The bound `p⁻¹` on the entries of `amiceMatrix` below the diagonal is less than one. -/
private theorem amiceBound_lt_one : (p : ℝ) ^ (-1 : ℤ) < 1 :=
  zpow_lt_one_of_neg₀ (by exact_mod_cast hp.out.one_lt) (by norm_num)

/-- The diagonal entries of `amiceMatrix` act isometrically under a contractive action. -/
private theorem norm_amiceMatrix_self_smul {E : Type*} [NormedAddCommGroup E] [Module ℤ_[p] E]
    [IsBoundedSMul ℤ_[p] E] (h k : ℕ) (e : E) : ‖amiceMatrix p h k k • e‖ = ‖e‖ :=
  NormedRing.norm_smul_of_isUnit_of_norm_eq_one
    (PadicInt.isUnit_iff.mpr (norm_amiceMatrix_self h k)) (norm_amiceMatrix_self h k) e

end Matrix

/-! ### Amice's theorem -/

variable {h : ℕ} {E : Type*} [NormedAddCommGroup E] [Module ℤ_[p] E] [IsBoundedSMul ℤ_[p] E]
  [IsUltrametricDist E] [CompleteSpace E]
  (S : Type*) [Semiring S] [Module S E] [ContinuousConstSMul S E] [SMulCommClass ℤ_[p] S E]

/-- Amice's map is the map defined by `amiceMatrix`, after reindexing its source by the block
reversal `amiceIndex` and its target by `amiceCoord`. -/
private theorem amiceMap_eq_congrLeft (c : C₀(ℕ, E)) :
    amiceMap p h S c = ZeroAtInftyContinuousMap.congrLeft S E
      (amiceCoord p h).toHomeomorphOfDiscrete
      ((amiceMatrix p h).toZeroAtInftySMulCLM S (tendsto_amiceMatrix h)
        ⟨1, norm_amiceMatrix_le h⟩
        (ZeroAtInftyContinuousMap.congrLeft S E (amicePerm p h).toHomeomorphOfDiscrete c)) := by
  ext i
  obtain ⟨k, rfl⟩ := (amiceCoord p h).surjective i
  refine (hasSum_amiceMap_apply S c _).unique ?_
  simp only [ZeroAtInftyContinuousMap.congrLeft_apply, Equiv.toHomeomorphOfDiscrete,
    Equiv.symm_toHomeomorph, Equiv.coe_toHomeomorph, Equiv.symm_apply_apply]
  rw [← (amicePerm p h).hasSum_iff]
  convert (amiceMatrix p h).hasSum_toZeroAtInftySMulCLM_apply S (tendsto_amiceMatrix h)
    ⟨1, norm_amiceMatrix_le h⟩ _ k using 2 with l
  simp [amicePerm, amiceMatrix_eq]

variable (p h) in
/-- **Amice's theorem.** Amice's map `(cₙ) ↦ ∑ₙ e_{h,n} • cₙ`, with
`e_{h,n}(x) = ⌊n / pʰ⌋! (x choose n)`, is an isometric isomorphism `C₀(ℕ, E) ≃ₗᵢ[S] LA_h(E)`.
For `E = ℤ_p` this is Amice's basis theorem `isOrthonormalBasis_amiceTerm`. -/
noncomputable def amiceEquiv : C₀(ℕ, E) ≃ₗᵢ[S] AnalyticStage p h E :=
  ((ZeroAtInftyContinuousMap.congrLeft S E (amicePerm p h).toHomeomorphOfDiscrete).trans
    ((amiceMatrix p h).toZeroAtInftySMulLinearIsometryEquiv S (tendsto_amiceMatrix h)
      (norm_amiceMatrix_le h) (fun k ↦ PadicInt.isUnit_iff.mpr (norm_amiceMatrix_self h k))
      (norm_amiceMatrix_self_smul h) amiceBound_lt_one
      (fun _ _ hlk ↦ norm_amiceMatrix_le_of_lt h hlk))).trans
    (ZeroAtInftyContinuousMap.congrLeft S E (amiceCoord p h).toHomeomorphOfDiscrete)

/-- Amice's isomorphism is Amice's map. -/
@[simp]
theorem amiceEquiv_apply (c : C₀(ℕ, E)) : amiceEquiv p h S c = amiceMap p h S c := by
  rw [amiceMap_eq_congrLeft, amiceEquiv, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.trans_apply, Matrix.toZeroAtInftySMulLinearIsometryEquiv_apply]

variable (p h) in
/-- **Amice's theorem: isometry.** Amice's map `(cₙ) ↦ ∑ₙ e_{h,n} • cₙ` preserves norms. -/
theorem norm_amiceMap (c : C₀(ℕ, E)) : ‖amiceMap p h S c‖ = ‖c‖ := by
  rw [← amiceEquiv_apply, LinearIsometryEquiv.norm_map]

variable (p h) in
/-- **Amice's theorem: surjectivity.** Every coefficient vector of `LA_h(E)` is the expansion of
a series `∑ₙ e_{h,n} • cₙ` with `cₙ → 0`. -/
theorem amiceMap_surjective : Function.Surjective (amiceMap p h S (E := E)) := fun v ↦
  ⟨(amiceEquiv p h S).symm v, by rw [← amiceEquiv_apply, LinearIsometryEquiv.apply_symm_apply]⟩

/-- The inverse of Amice's isomorphism sends Amice's vector `e_{h,n} • e` to the coordinate vector
`single n e`. -/
@[simp]
theorem amiceEquiv_symm_amiceTerm (n : ℕ) (e : E) :
    (amiceEquiv p h S).symm (amiceTerm p h n e) = ZeroAtInftyContinuousMap.single n e := by
  rw [LinearIsometryEquiv.symm_apply_eq, amiceEquiv_apply, amiceMap_single]

variable (p h) in
/-- **Amice's basis theorem.** The disc expansions `amiceTerm p h n 1` of Amice's polynomials
`e_{h,n}(x) = ⌊n / pʰ⌋! (x choose n)` form an orthonormal basis of `LA_h(ℤ_p)`. -/
theorem isOrthonormalBasis_amiceTerm :
    IsOrthonormalBasis ℤ_[p] fun n ↦ amiceTerm p h n (1 : ℤ_[p]) := by
  simpa using (amiceEquiv p h ℤ_[p] (E := ℤ_[p])).symm.isOrthonormalBasis_symm_single

end AnalyticStage

end TauCeti
