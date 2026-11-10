/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Distribution.Amice.Basis
public import TauCeti.Analysis.Normed.Module.Bases.Orthonormal
public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Triangular

/-!
# Amice's theorem on the analytic stages

For a complete ultrametric normed `ℤ_p`-module `E` with contractive action, Amice's map

`TauCeti.AnalyticStage.amiceMap p h S : C₀(ℕ, E) → LA_h(E)`,  `(cₙ) ↦ ∑ₙ e_{h,n} • cₙ`,

built from the polynomials `e_{h,n}(x) = ⌊n / pʰ⌋! (x choose n)`, is an isometric isomorphism
(`TauCeti.AnalyticStage.amiceEquiv`). Every coefficient vector in the analytic stage
`LA_h(E) = C₀(ZMod (pʰ) × ℕ, E)` is therefore the expansion of a unique series `∑ₙ e_{h,n} • cₙ`
with `cₙ → 0`, and its norm is `supₙ ‖cₙ‖`. No torsion-freeness of `E` is needed.

The proof writes Amice's map as a matrix over `ℤ_p` and applies the criterion
`Matrix.toZeroAtInftySMulLinearIsometryEquiv` for triangular perturbations of the identity.
Write `n = pʰ q + r` with `r < pʰ`. Modulo `p`, the expansion of `e_{h,n}` on the disc of a
natural centre `a < pʰ` vanishes in degrees above `q`
(`TauCeti.norm_coeff_amicePolynomial_lt_one_of_div_lt`), vanishes entirely when `a < r`
(`TauCeti.norm_coeff_amicePolynomial_lt_one_of_mod_lt`), and has a unit coefficient in degree `q`
when `a = r` (`TauCeti.norm_coeff_amicePolynomial_mod_div`). Order the coordinates `(a, j)` of
`LA_h(E)` by the degree `j` first and then by *decreasing* centre `a`, so that `(a, j)` comes at
position `pʰ j + (pʰ - 1 - a)`; this reversal of the centres is the passage from Colmez's centres
`-a`, `1 ≤ a ≤ pʰ`, to the natural residue representatives used by `LA_h`. Reindex Amice's index
`n` in the same way. In these coordinates the coefficient of `e_{h,n}` at its own position
`(r, q)` is a unit, and every coefficient below the diagonal is divisible by `p`.

## Main definitions

* `TauCeti.AnalyticStage.amiceEquiv p h S`: Amice's map as an `S`-linear isometric equivalence
  `C₀(ℕ, E) ≃ₗᵢ[S] LA_h(E)`.

## Main results

* `TauCeti.AnalyticStage.amiceEquiv_apply`: `amiceEquiv` is `amiceMap`.
* `TauCeti.AnalyticStage.norm_amiceMap`: Amice's map preserves norms.

## References

* Y. Amice, *Interpolation p-adique*, Bull. Soc. Math. France 92 (1964), 117–180.
* P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010), §I.4.
-/

public section

open Filter Topology Polynomial ZeroAtInftyContinuousMap
open scoped ZeroAtInfty

variable {p : ℕ} [hp : Fact p.Prime]

namespace TauCeti.AnalyticStage

/-! ### Reordering the coordinates -/

variable (p) in
/-- Reversal of the residues within each block of `pʰ` consecutive integers:
`pʰ q + s ↦ pʰ q + (pʰ - 1 - s)` for `s < pʰ`. -/
private def rev (h k : ℕ) : ℕ := p ^ h * (k / p ^ h) + (p ^ h - 1 - k % p ^ h)

private theorem rev_lt (h k : ℕ) : p ^ h - 1 - k % p ^ h < p ^ h :=
  (Nat.sub_le _ _).trans_lt (Nat.sub_lt (pow_pos hp.out.pos h) one_pos)

private theorem rev_div (h k : ℕ) : rev p h k / p ^ h = k / p ^ h := by
  rw [rev, Nat.mul_add_div (pow_pos hp.out.pos h), Nat.div_eq_of_lt (rev_lt h k), add_zero]

private theorem rev_mod (h k : ℕ) : rev p h k % p ^ h = p ^ h - 1 - k % p ^ h := by
  rw [rev, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt (rev_lt h k)]

private theorem rev_rev (h k : ℕ) : rev p h (rev p h k) = k := by
  have hk := Nat.mod_lt k (pow_pos hp.out.pos h)
  have hdm := Nat.div_add_mod k (p ^ h)
  rw [rev, rev_div, rev_mod]
  generalize k % p ^ h = s at *
  generalize p ^ h * (k / p ^ h) = m at *
  omega

variable (p) in
/-- The reversal of the residues in each block, as a permutation of `ℕ`. -/
private def revPerm (h : ℕ) : Equiv.Perm ℕ :=
  Function.Involutive.toPerm (rev p h) (rev_rev h)

private theorem revPerm_apply (h k : ℕ) : revPerm p h k = rev p h k := rfl

private theorem revPerm_symm (h : ℕ) : (revPerm p h).symm = revPerm p h :=
  Function.Involutive.toPerm_symm _

variable (p) in
/-- The coordinate `(a, j)` of `LA_h` placed at position `pʰ j + (pʰ - 1 - a.val)`: the
coordinates are ordered by degree, and then by decreasing centre. -/
private def coordEquiv (h : ℕ) : ℕ ≃ ZMod (p ^ h) × ℕ :=
  (revPerm p h).trans (Nat.residueClassesEquiv (p ^ h))

private theorem val_coordEquiv_fst (h i : ℕ) : (coordEquiv p h i).1.val = rev p h i % p ^ h :=
  ZMod.val_natCast _ _

private theorem coordEquiv_snd (h i : ℕ) : (coordEquiv p h i).2 = i / p ^ h :=
  rev_div h i

/-! ### The matrix of Amice's map -/

variable (p) in
/-- The matrix of Amice's map in the reordered coordinates: its entry `(i, k)` is the
coefficient, at the coordinate in position `i`, of the expansion of `e_{h,n}` with `n = rev k`. -/
private noncomputable def amiceMatrix (h : ℕ) : Matrix ℕ ℕ ℤ_[p] := fun i k ↦
  (amicePolynomial p h (rev p h k) ((coordEquiv p h i).1.val : ℤ_[p])).coeff (coordEquiv p h i).2

/-- The columns of `amiceMatrix` tend to zero: they are the coefficients of Amice's vectors. -/
private theorem tendsto_amiceMatrix (h k : ℕ) :
    Tendsto (fun i ↦ amiceMatrix p h i k) cofinite (𝓝 0) := by
  have := (amiceTerm p h (rev p h k) (1 : ℤ_[p])).tendsto_cofinite.comp
    (coordEquiv p h).injective.tendsto_cofinite
  simpa [Function.comp_def, amiceMatrix] using this

/-- The diagonal entries of `amiceMatrix` are units. -/
private theorem isUnit_amiceMatrix (h i : ℕ) : IsUnit (amiceMatrix p h i i) := by
  rw [amiceMatrix, val_coordEquiv_fst, coordEquiv_snd, ← rev_div h i]
  exact PadicInt.isUnit_iff.mpr (norm_coeff_amicePolynomial_mod_div h (rev p h i))

/-- The entries of `amiceMatrix` below the diagonal are divisible by `p`. -/
private theorem dvd_amiceMatrix (h : ℕ) {i k : ℕ} (hki : k < i) :
    (p : ℤ_[p]) ∣ amiceMatrix p h i k := by
  have hP : 0 < p ^ h := pow_pos hp.out.pos h
  rw [amiceMatrix, val_coordEquiv_fst, coordEquiv_snd, ← PadicInt.norm_lt_one_iff_dvd]
  rcases (Nat.div_le_div_right (c := p ^ h) hki.le).lt_or_eq with hlt | heq
  · exact norm_coeff_amicePolynomial_lt_one_of_div_lt _ (by rwa [rev_div])
  · -- In the same block, `k` has the smaller residue, so `rev i` has the smaller residue.
    refine norm_coeff_amicePolynomial_lt_one_of_mod_lt ?_ _
    rw [Nat.mod_mod]
    have hk := Nat.div_add_mod k (p ^ h)
    have hi := Nat.div_add_mod i (p ^ h)
    have hi' := Nat.mod_lt i hP
    rw [rev_mod, rev_mod, heq] at *
    generalize k % p ^ h = s at *
    generalize i % p ^ h = t at *
    generalize p ^ h * (i / p ^ h) = m at *
    omega

/-! ### Amice's isometry -/

variable {h : ℕ} {E : Type*} [NormedAddCommGroup E] [Module ℤ_[p] E] [IsBoundedSMul ℤ_[p] E]
  [IsUltrametricDist E] [CompleteSpace E]
  (S : Type*) [Semiring S] [Module S E] [ContinuousConstSMul S E] [SMulCommClass ℤ_[p] S E]

variable (p h) in
/-- **Amice's theorem.** Amice's map `(cₙ) ↦ ∑ₙ e_{h,n} • cₙ`, where
`e_{h,n}(x) = ⌊n / pʰ⌋! (x choose n)`, is an isometric isomorphism from the null sequences in `E`
onto the analytic stage `LA_h(E)`. -/
noncomputable def amiceEquiv : C₀(ℕ, E) ≃ₗᵢ[S] AnalyticStage p h E :=
  (congrLeft S E (revPerm p h).toHomeomorphOfDiscrete).trans <|
    ((amiceMatrix p h).toZeroAtInftySMulLinearIsometryEquiv S (tendsto_amiceMatrix h)
      (fun _ _ ↦ PadicInt.norm_le_one _) (isUnit_amiceMatrix h)
      (fun i ↦ PadicInt.norm_smul_of_isUnit (isUnit_amiceMatrix h i))
      (c := (p : ℝ)⁻¹) (inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)) fun i k hki ↦ by
        obtain ⟨x, hx⟩ := dvd_amiceMatrix (p := p) h hki
        rw [hx, norm_mul, PadicInt.norm_p]
        exact mul_le_of_le_one_right (by positivity) (PadicInt.norm_le_one x)).trans
      (congrLeft S E (coordEquiv p h).toHomeomorphOfDiscrete)

/-- The isometric equivalence `amiceEquiv` is Amice's map. -/
@[simp]
theorem amiceEquiv_apply (c : C₀(ℕ, E)) : amiceEquiv p h S c = amiceMap p h S c := by
  ext x
  simp only [amiceEquiv, LinearIsometryEquiv.trans_apply, congrLeft_apply,
    Matrix.toZeroAtInftySMulLinearIsometryEquiv_apply]
  refine ((amiceMatrix p h).hasSum_toZeroAtInftySMulCLM_apply S _ _ _ _).unique ?_
  refine (Equiv.hasSum_iff (revPerm p h)).1 ?_
  convert hasSum_amiceMap_apply S c x using 2 with n
  simp [amiceMatrix, Equiv.toHomeomorphOfDiscrete, revPerm_symm, revPerm_apply, rev_rev]

/-- **Amice's theorem.** Amice's map preserves norms: `‖∑ₙ e_{h,n} • cₙ‖ = supₙ ‖cₙ‖`. -/
@[simp]
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

/-- Continuous linear maps out of an analytic stage agreeing on Amice's polynomials are
equal. -/
theorem continuousLinearMap_ext_amiceTerm {R M : Type*} [NormedCommRing R]
    [Algebra ℤ_[p] R] [IsBoundedSMul ℤ_[p] R] [IsUltrametricDist R] [CompleteSpace R]
    [AddCommMonoid M] [Module R M] [TopologicalSpace M] [T2Space M]
    {φ ψ : AnalyticStage p h R →L[R] M}
    (H : ∀ n, φ (amiceTerm p h n 1) = ψ (amiceTerm p h n 1)) : φ = ψ := by
  have heq : φ ∘L (amiceEquiv p h R).toContinuousLinearEquiv.toContinuousLinearMap =
      ψ ∘L (amiceEquiv p h R).toContinuousLinearEquiv.toContinuousLinearMap := by
    apply continuousLinearMap_ext_single_one
    intro n
    simpa only [ContinuousLinearMap.comp_apply, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      ContinuousLinearEquiv.coe_coe, amiceEquiv_apply, amiceMap_single] using H n
  ext c
  simpa only [ContinuousLinearMap.comp_apply, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.apply_symm_apply] using
    DFunLike.congr_fun heq ((amiceEquiv p h R).symm c)

end TauCeti.AnalyticStage
