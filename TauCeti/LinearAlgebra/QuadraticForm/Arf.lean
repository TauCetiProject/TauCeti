/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.ZMod.IntUnitsPower
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
public import Mathlib.LinearAlgebra.QuadraticForm.Prod
public import Mathlib.LinearAlgebra.SymplecticGroup
import Mathlib.FieldTheory.Finiteness
import Mathlib.Tactic.LinearCombination
import TauCeti.Data.ZMod.IntUnitsPower
import TauCeti.LinearAlgebra.BilinearForm.Prod
import TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis
import TauCeti.LinearAlgebra.QuadraticForm.Basic
import TauCeti.LinearAlgebra.QuadraticForm.Isometry

/-!
# The Arf invariant of a quadratic form over `𝔽₂`

Let `q` be a quadratic form on a finite-dimensional vector space `V` over `𝔽₂ = ZMod 2` whose
polar form `q.polarBilin` is nondegenerate. In characteristic two the polar form is alternating,
so `V` has a *symplectic basis* `a₁, …, aₘ, b₁, …, bₘ` for it: the polar form pairs `aᵢ` with `bᵢ`
to `1` and every other pair of basis vectors to `0`. The **Arf invariant** of `q` is
`Arf(q) = ∑ᵢ q(aᵢ) q(bᵢ) ∈ 𝔽₂`.

The sum `∑ᵢ q(aᵢ)` itself depends on the basis; the sum of products does not. This is proved with
the *Gauss sum* of `q`: writing a vector in coordinates and using that distinct planes
`span {aᵢ, bᵢ}` are orthogonal, the sum `∑ᵥ (-1)^{q(v)}` factors as a product over the planes,
and each plane contributes `2 (-1)^{q(aᵢ) q(bᵢ)}`, so
`∑ᵥ (-1)^{q(v)} = (-1)^{Arf(q)} 2^m`. The left side involves no choice of basis. The same formula
gives isometry invariance and additivity on orthogonal sums, since the Gauss sum of an orthogonal
sum is the product of the Gauss sums, and it counts the zeros of `q`: for `dim V = 2m` with
`m ≥ 1`, the form `q` has `2^{2m-1} + (-1)^{Arf(q)} 2^{m-1}` zeros.

The Arf invariant is the invariant of the quadratic refinements that occur in topology: the Arf
invariant of a knot, and the Kervaire invariant of a framed manifold, which is the surgery
obstruction in dimensions `4k + 2`.

## Main definitions

* `QuadraticMap.arf`: the Arf invariant of a quadratic form over `ZMod 2`, computed in a chosen
  symplectic basis of its polar form, and `0` when the polar form has no symplectic basis.

## Main results

* `QuadraticMap.sum_neg_one_uzpow_eq_of_basis`: the Gauss sum of `q` computed in a symplectic
  basis.
* `QuadraticMap.arf_eq_sum`: the Arf invariant equals `∑ᵢ q(aᵢ) q(bᵢ)` in *every* symplectic
  basis; `QuadraticMap.arf_eq_zero_of_not_exists_basis` and
  `QuadraticMap.arf_eq_zero_of_not_nondegenerate` give the cases without a symplectic basis.
* `QuadraticMap.sum_neg_one_uzpow_eq`: the Gauss sum formula `∑ᵥ (-1)^{q(v)} = (-1)^{Arf(q)} 2^m`.
* `QuadraticMap.arf_congr`: isometric forms have the same Arf invariant.
* `QuadraticMap.arf_prod`: the Arf invariant is additive on orthogonal sums.
* `QuadraticMap.card_filter_apply_eq_zero_eq`: the number of zeros of `q`.
* `QuadraticMap.arf_eq_mul_of_polar_eq_one`: the Arf invariant of a binary form.
* `QuadraticMap.arf_linMulLin_fst_snd`,
  `QuadraticMap.arf_sq_comp_fst_add_linMulLin_fst_snd_add_sq_comp_snd`: the hyperbolic plane `xy`
  has Arf invariant `0` and the anisotropic plane `x² + xy + y²` has Arf invariant `1`.

## References

* C. Arf, *Untersuchungen über quadratische Formen in Körpern der Charakteristik 2 (Teil I)*,
  J. Reine Angew. Math. 183 (1941), 148–167.
* A. Pyronneau, *The Arf and Rohklin's invariant*, January 2024,
  https://web.ma.utexas.edu/SMC/2024/Rokhlin_s_Invariant.pdf, §2.1, Lemmas 2.11–2.13,
  Corollary 2.14 and Theorem 2.15, pp. 4–5.
-/

public section

noncomputable section

open Module
open LinearMap (BilinForm)

namespace QuadraticMap

variable {V V₁ V₂ : Type*} [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup V₁]
  [Module (ZMod 2) V₁] [AddCommGroup V₂] [Module (ZMod 2) V₂]

section Sign

/-- The four-term sum behind the Gauss sum of a hyperbolic pair, as an identity in `𝔽₂`. -/
private theorem sum_neg_one_uzpow_two : ∀ α β : ZMod 2,
    ∑ x : ZMod 2, ∑ y : ZMod 2, (((-1 : ℤˣ) ^ (x * α + y * β + x * y) : ℤˣ) : ℤ) =
      2 * (((-1 : ℤˣ) ^ (α * β) : ℤˣ) : ℤ) := by
  decide

end Sign

section Plane

variable (q : QuadraticForm (ZMod 2) V)

/-- The value of `q` on a vector of a plane spanned by `a, b` with `polar q a b = 1`. -/
private theorem apply_smul_add_smul {a b : V} (hab : polar q a b = 1) (x y : ZMod 2) :
    q (x • a + y • b) = x * q a + y * q b + x * y := by
  rw [QuadraticMap.map_add q, polar_smul_left, polar_smul_right, hab, QuadraticMap.map_smul q,
    QuadraticMap.map_smul q, smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul]
  generalize q a = α
  generalize q b = β
  revert x y α β
  decide

/-- **The Gauss sum of a hyperbolic pair.** If `polar q a b = 1`, the sum of `(-1)^{q(v)}` over the
four vectors `v = x a + y b` of the plane they span is `2 (-1)^{q(a) q(b)}`. -/
private theorem sum_neg_one_uzpow_plane {a b : V} (hab : polar q a b = 1) :
    ∑ p : ZMod 2 × ZMod 2, (((-1 : ℤˣ) ^ q (p.1 • a + p.2 • b) : ℤˣ) : ℤ) =
      2 * (((-1 : ℤˣ) ^ (q a * q b) : ℤˣ) : ℤ) := by
  simp_rw [apply_smul_add_smul q hab]
  rw [Fintype.sum_prod_type]
  exact sum_neg_one_uzpow_two _ _

end Plane

section SymplecticBasis

variable {q : QuadraticForm (ZMod 2) V} {m : ℕ} {b : Basis (Fin m ⊕ Fin m) (ZMod 2) V}

/-- In a symplectic basis, the polar form pairs the basis vectors by the entries of `Matrix.J`. -/
private theorem polar_apply_eq_J
    (hb : BilinForm.toMatrix b q.polarBilin = Matrix.J (Fin m) (ZMod 2)) (x y : Fin m ⊕ Fin m) :
    polar q (b x) (b y) = Matrix.J (Fin m) (ZMod 2) x y := by
  rw [← polarBilin_apply_apply, ← BilinForm.toMatrix_apply, hb]

/-- In a symplectic basis, `aᵢ = b (inl i)` pairs with `bᵢ = b (inr i)` to `1`. -/
private theorem polar_inl_inr
    (hb : BilinForm.toMatrix b q.polarBilin = Matrix.J (Fin m) (ZMod 2)) (i : Fin m) :
    polar q (b (.inl i)) (b (.inr i)) = 1 := by
  rw [polar_apply_eq_J hb]
  simp [Matrix.J]

/-- In a symplectic basis, the planes `span {aᵢ, bᵢ}` and `span {aⱼ, bⱼ}` are orthogonal for
`i ≠ j`. -/
private theorem polar_plane_eq_zero
    (hb : BilinForm.toMatrix b q.polarBilin = Matrix.J (Fin m) (ZMod 2)) {i j : Fin m}
    (hij : i ≠ j) (x y x' y' : ZMod 2) :
    polar q (x • b (.inl i) + y • b (.inr i)) (x' • b (.inl j) + y' • b (.inr j)) = 0 := by
  simp only [polar_add_left, polar_add_right, polar_smul_left, polar_smul_right,
    polar_apply_eq_J hb]
  simp [Matrix.J, Matrix.fromBlocks, hij]

/-- The coordinate identification `(Fin m → 𝔽₂ × 𝔽₂) ≃ V` sending `c` to
`∑ᵢ (c i).1 • aᵢ + (c i).2 • bᵢ`. -/
private def planeEquiv (b : Basis (Fin m ⊕ Fin m) (ZMod 2) V) :
    (Fin m → ZMod 2 × ZMod 2) ≃ V :=
  (Equiv.arrowProdEquivProdArrow (Fin m) (fun _ => ZMod 2) (fun _ => ZMod 2)).trans
    ((Equiv.sumArrowEquivProdArrow (Fin m) (Fin m) (ZMod 2)).symm.trans b.equivFun.symm.toEquiv)

private theorem planeEquiv_apply (b : Basis (Fin m ⊕ Fin m) (ZMod 2) V)
    (c : Fin m → ZMod 2 × ZMod 2) :
    planeEquiv b c = ∑ i, ((c i).1 • b (.inl i) + (c i).2 • b (.inr i)) := by
  simp [planeEquiv, Basis.equivFun_symm_apply, Fintype.sum_sum_type, Finset.sum_add_distrib,
    Equiv.sumArrowEquivProdArrow, Equiv.arrowProdEquivProdArrow]

variable (q b) in
/-- **The Gauss sum in a symplectic basis.** If `aᵢ = b (inl i)`, `bᵢ = b (inr i)` form a
symplectic basis for the polar form of `q`, then `∑ᵥ (-1)^{q(v)} = (-1)^{∑ᵢ q(aᵢ) q(bᵢ)} 2^m`. -/
theorem sum_neg_one_uzpow_eq_of_basis [Fintype V]
    (hb : BilinForm.toMatrix b q.polarBilin = Matrix.J (Fin m) (ZMod 2)) :
    ∑ v, (((-1 : ℤˣ) ^ q v : ℤˣ) : ℤ) =
      (((-1 : ℤˣ) ^ (∑ i, q (b (.inl i)) * q (b (.inr i))) : ℤˣ) : ℤ) * 2 ^ m := by
  -- Sum over the coordinates of `v` in the planes `span {aᵢ, bᵢ}`.
  rw [← (planeEquiv b).sum_comp]
  -- The planes are orthogonal, so `q` is additive across them and the sign factors.
  have hq : ∀ c : Fin m → ZMod 2 × ZMod 2, q (planeEquiv b c) =
      ∑ i, q ((c i).1 • b (.inl i) + (c i).2 • b (.inr i)) := fun c => by
    rw [planeEquiv_apply]
    exact q.map_sum_of_polar_eq_zero _ _ fun i _ j _ hij => polar_plane_eq_zero hb hij _ _ _ _
  simp_rw [hq, TauCeti.uzpow_sum, Units.coe_prod]
  -- Each plane contributes `2 (-1)^{q(aᵢ) q(bᵢ)}`.
  rw [← Fintype.prod_sum (fun i (p : ZMod 2 × ZMod 2) =>
    (((-1 : ℤˣ) ^ q (p.1 • b (.inl i) + p.2 • b (.inr i)) : ℤˣ) : ℤ))]
  simp_rw [sum_neg_one_uzpow_plane q (polar_inl_inr hb _)]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_comm]

end SymplecticBasis

variable (q : QuadraticForm (ZMod 2) V)

open Classical in
/-- The **Arf invariant** of a quadratic form `q` over `𝔽₂ = ZMod 2`: for a symplectic basis
`aᵢ = b (inl i)`, `bᵢ = b (inr i)` of the polar form of `q`, it is `∑ᵢ q(aᵢ) q(bᵢ)`. This does not
depend on the basis (`QuadraticMap.arf_eq_sum`). When the polar form has no symplectic basis, that
is when it is degenerate or `V` is infinite-dimensional, it is `0` by convention. -/
def arf : ZMod 2 :=
  if h : ∃ (m : ℕ) (b : Basis (Fin m ⊕ Fin m) (ZMod 2) V),
      BilinForm.toMatrix b q.polarBilin = Matrix.J (Fin m) (ZMod 2) then
    ∑ i, q (h.choose_spec.choose (.inl i)) * q (h.choose_spec.choose (.inr i))
  else 0

variable {q}

/-- The sum `∑ᵢ q(aᵢ) q(bᵢ)` is the same in any two symplectic bases: both are read off the Gauss
sum of `q`. -/
private theorem sum_mul_eq_of_basis {m m' : ℕ} {b : Basis (Fin m ⊕ Fin m) (ZMod 2) V}
    {b' : Basis (Fin m' ⊕ Fin m') (ZMod 2) V}
    (hb : BilinForm.toMatrix b q.polarBilin = Matrix.J (Fin m) (ZMod 2))
    (hb' : BilinForm.toMatrix b' q.polarBilin = Matrix.J (Fin m') (ZMod 2)) :
    ∑ i, q (b (.inl i)) * q (b (.inr i)) = ∑ i, q (b' (.inl i)) * q (b' (.inr i)) := by
  have : Module.Finite (ZMod 2) V := Module.Finite.of_basis b
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have := Fintype.ofFinite V
  -- Both bases have `finrank V` vectors.
  obtain rfl : m' = m := by
    have h₁ := finrank_eq_card_basis b
    have h₂ := finrank_eq_card_basis b'
    simp only [Fintype.card_sum, Fintype.card_fin] at h₁ h₂
    omega
  have hg := (sum_neg_one_uzpow_eq_of_basis q b hb).symm.trans
    (sum_neg_one_uzpow_eq_of_basis q b' hb')
  exact TauCeti.neg_one_uzpow_injective
    (Units.ext (mul_right_cancel₀ (pow_ne_zero _ two_ne_zero) hg))

/-- **The Arf invariant does not depend on the symplectic basis**: in every symplectic basis
`aᵢ = b (inl i)`, `bᵢ = b (inr i)` of the polar form of `q`, `Arf(q) = ∑ᵢ q(aᵢ) q(bᵢ)`. -/
theorem arf_eq_sum {m : ℕ} (b : Basis (Fin m ⊕ Fin m) (ZMod 2) V)
    (hb : BilinForm.toMatrix b q.polarBilin = Matrix.J (Fin m) (ZMod 2)) :
    q.arf = ∑ i, q (b (.inl i)) * q (b (.inr i)) := by
  rw [arf]
  split_ifs with h
  · exact sum_mul_eq_of_basis h.choose_spec.choose_spec hb
  · exact absurd ⟨m, b, hb⟩ h

/-- The Arf invariant is `0` by convention when the polar form has no symplectic basis, for instance
when `V` is infinite-dimensional. -/
theorem arf_eq_zero_of_not_exists_basis
    (h : ¬ ∃ (m : ℕ) (b : Basis (Fin m ⊕ Fin m) (ZMod 2) V),
      BilinForm.toMatrix b q.polarBilin = Matrix.J (Fin m) (ZMod 2)) :
    q.arf = 0 := by
  rw [arf, dite_eq_right h]

/-- The Arf invariant of a form whose polar form is degenerate is `0` by convention: a symplectic
basis makes the polar form nondegenerate, since `Matrix.J` is invertible. -/
theorem arf_eq_zero_of_not_nondegenerate (hq : ¬ q.polarBilin.Nondegenerate) : q.arf = 0 :=
  arf_eq_zero_of_not_exists_basis fun ⟨m, b, hb⟩ => hq <|
    (BilinForm.nondegenerate_iff_det_ne_zero b).mpr <| by
      rw [hb]
      exact (Matrix.isUnit_det_J (Fin m) (ZMod 2)).ne_zero

/-- **The Gauss sum formula.** If the polar form of `q` is nondegenerate on the finite space `V`,
of dimension `2 m`, then `∑ᵥ (-1)^{q(v)} = (-1)^{Arf(q)} 2^m`. -/
theorem sum_neg_one_uzpow_eq [Fintype V] (hq : q.polarBilin.Nondegenerate) :
    ∑ v, (((-1 : ℤˣ) ^ q v : ℤˣ) : ℤ) =
      (((-1 : ℤˣ) ^ q.arf : ℤˣ) : ℤ) * 2 ^ (finrank (ZMod 2) V / 2) := by
  obtain ⟨m, b, hb⟩ := BilinForm.IsAlt.exists_basis_toMatrix_eq_J q.isAlt_polarBilin hq
  have hm : finrank (ZMod 2) V / 2 = m := by
    rw [finrank_eq_card_basis b, Fintype.card_sum, Fintype.card_fin]
    omega
  rw [hm, arf_eq_sum b hb, sum_neg_one_uzpow_eq_of_basis q b hb]

/-- Isometric quadratic forms over `ZMod 2` have the same Arf invariant. -/
theorem arf_congr {q₁ : QuadraticForm (ZMod 2) V₁} {q₂ : QuadraticForm (ZMod 2) V₂}
    (e : q₁.IsometryEquiv q₂) : q₁.arf = q₂.arf := by
  by_cases h : ∃ (m : ℕ) (b : Basis (Fin m ⊕ Fin m) (ZMod 2) V₁),
      BilinForm.toMatrix b q₁.polarBilin = Matrix.J (Fin m) (ZMod 2)
  · obtain ⟨m, b, hb⟩ := h
    rw [arf_eq_sum b hb, arf_eq_sum _ ((e.toMatrix_polarBilin_basis_map b).trans hb)]
    simp [IsometryEquiv.map_app]
  · rw [arf_eq_zero_of_not_exists_basis h, arf_eq_zero_of_not_exists_basis (q := q₂)
      fun ⟨m, b, hb⟩ => h ⟨m, b.map e.symm.toLinearEquiv,
        (e.symm.toMatrix_polarBilin_basis_map b).trans hb⟩]

/-- **The Arf invariant is additive on orthogonal sums** of forms with nondegenerate polar forms
on finite-dimensional spaces. -/
theorem arf_prod [FiniteDimensional (ZMod 2) V₁] [FiniteDimensional (ZMod 2) V₂]
    {q₁ : QuadraticForm (ZMod 2) V₁} {q₂ : QuadraticForm (ZMod 2) V₂}
    (hq₁ : q₁.polarBilin.Nondegenerate) (hq₂ : q₂.polarBilin.Nondegenerate) :
    (q₁.prod q₂).arf = q₁.arf + q₂.arf := by
  have : Finite V₁ := Module.finite_of_finite (ZMod 2)
  have : Finite V₂ := Module.finite_of_finite (ZMod 2)
  have := Fintype.ofFinite V₁
  have := Fintype.ofFinite V₂
  have hq : (q₁.prod q₂).polarBilin.Nondegenerate :=
    nondegenerate_polarBilin_prod_iff.mpr ⟨hq₁, hq₂⟩
  -- The Gauss sum of the orthogonal sum is the product of the Gauss sums.
  have hg := sum_neg_one_uzpow_eq hq
  rw [Fintype.sum_prod_type] at hg
  simp_rw [prod_apply, uzpow_add, Units.val_mul, ← Finset.mul_sum, ← Finset.sum_mul,
    sum_neg_one_uzpow_eq hq₁, sum_neg_one_uzpow_eq hq₂] at hg
  have hm : finrank (ZMod 2) (V₁ × V₂) / 2 =
      finrank (ZMod 2) V₁ / 2 + finrank (ZMod 2) V₂ / 2 := by
    have := BilinForm.IsAlt.even_finrank q₁.isAlt_polarBilin hq₁
    have := BilinForm.IsAlt.even_finrank q₂.isAlt_polarBilin hq₂
    rw [finrank_prod]
    obtain ⟨k₁, hk₁⟩ := ‹Even (finrank (ZMod 2) V₁)›
    obtain ⟨k₂, hk₂⟩ := ‹Even (finrank (ZMod 2) V₂)›
    omega
  rw [hm, pow_add] at hg
  refine TauCeti.neg_one_uzpow_injective (Units.ext ?_)
  dsimp only
  rw [uzpow_add, Units.val_mul]
  refine mul_right_cancel₀ (pow_ne_zero _ two_ne_zero :
    (2 : ℤ) ^ (finrank (ZMod 2) V₁ / 2 + finrank (ZMod 2) V₂ / 2) ≠ 0) ?_
  rw [pow_add, ← hg]
  ring

/-- **The number of zeros of a quadratic form over `ZMod 2`.** If the polar form of `q` is
nondegenerate on a space of dimension `2 (m + 1)`, then `q` has
`2^{2m+1} + (-1)^{Arf(q)} 2^m` zeros. -/
theorem card_filter_apply_eq_zero_eq [Fintype V] (hq : q.polarBilin.Nondegenerate)
    {m : ℕ} (hm : finrank (ZMod 2) V = 2 * (m + 1)) :
    ((Finset.univ.filter fun v => q v = 0).card : ℤ) =
      2 ^ (2 * m + 1) + (((-1 : ℤˣ) ^ q.arf : ℤˣ) : ℤ) * 2 ^ m := by
  have hg := sum_neg_one_uzpow_eq hq
  rw [hm, Nat.mul_div_cancel_left _ two_pos] at hg
  -- Each zero contributes `+1` and each nonzero value `-1` to the Gauss sum.
  have hsum : ∑ v, (((-1 : ℤˣ) ^ q v : ℤˣ) : ℤ) =
      2 * ((Finset.univ.filter fun v => q v = 0).card : ℤ) - 2 ^ (2 * (m + 1)) := by
    have h : ∀ v, (((-1 : ℤˣ) ^ q v : ℤˣ) : ℤ) = 2 * (if q v = 0 then 1 else 0) - 1 := fun v => by
      rw [TauCeti.coe_neg_one_uzpow_eq_ite]
      split_ifs <;> norm_num
    simp_rw [h]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_boole, Finset.sum_const,
      Finset.card_univ, Module.card_eq_pow_finrank (K := ZMod 2), hm, ZMod.card]
    simp
  rw [hsum] at hg
  refine mul_left_cancel₀ (two_ne_zero : (2 : ℤ) ≠ 0) ?_
  linear_combination hg

/-! ### The two planes -/

/-- **The Arf invariant of a binary form.** A quadratic form on `𝔽₂²` whose polar form pairs the
standard basis vectors to `1` has Arf invariant `q(1, 0) q(0, 1)`. -/
theorem arf_eq_mul_of_polar_eq_one {q : QuadraticForm (ZMod 2) (ZMod 2 × ZMod 2)}
    (hq : polar q (1, 0) (0, 1) = 1) : q.arf = q (1, 0) * q (0, 1) := by
  let b := (Basis.singleton (Fin 1) (ZMod 2)).prod (Basis.singleton (Fin 1) (ZMod 2))
  have hb₁ : b (.inl 0) = (1, 0) := by simp [b]
  have hb₂ : b (.inr 0) = (0, 1) := by simp [b]
  have hb : BilinForm.toMatrix b q.polarBilin = Matrix.J (Fin 1) (ZMod 2) := by
    ext x y
    rw [BilinForm.toMatrix_apply]
    rcases x with x | x <;> rcases y with y | y <;> obtain rfl := Subsingleton.elim x 0 <;>
      obtain rfl := Subsingleton.elim y 0 <;>
      simp [hb₁, hb₂, polar_self, polar_comm q (0, 1), hq, Matrix.J,
        (by decide : (2 : ZMod 2) = 0)]
  rw [arf_eq_sum b hb, Fin.sum_univ_one, hb₁, hb₂]

/-- The **hyperbolic plane** `q(x, y) = xy` over `ZMod 2` has Arf invariant `0`. -/
@[simp]
theorem arf_linMulLin_fst_snd :
    (linMulLin (LinearMap.fst (ZMod 2) (ZMod 2) (ZMod 2))
      (LinearMap.snd (ZMod 2) (ZMod 2) (ZMod 2))).arf = 0 := by
  rw [arf_eq_mul_of_polar_eq_one] <;> simp [polar]

/-- The **anisotropic plane** `q(x, y) = x² + xy + y²` over `ZMod 2` has Arf invariant `1`. -/
@[simp]
theorem arf_sq_comp_fst_add_linMulLin_fst_snd_add_sq_comp_snd :
    (sq.comp (LinearMap.fst (ZMod 2) (ZMod 2) (ZMod 2)) +
      linMulLin (LinearMap.fst (ZMod 2) (ZMod 2) (ZMod 2))
        (LinearMap.snd (ZMod 2) (ZMod 2) (ZMod 2)) +
      sq.comp (LinearMap.snd (ZMod 2) (ZMod 2) (ZMod 2))).arf = 1 := by
  rw [arf_eq_mul_of_polar_eq_one] <;> simp [polar]

end QuadraticMap
