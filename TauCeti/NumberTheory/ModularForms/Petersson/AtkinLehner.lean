/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.AtkinLehner.Normalized
public import TauCeti.NumberTheory.ModularForms.Fricke.Normalized
public import TauCeti.NumberTheory.ModularForms.Petersson.Unitary

/-!
# The Fricke and Atkin–Lehner operators are Petersson-unitary

The Fricke matrix `W_N = !![0, -1; N, 0]` normalises `Γ₁(N)`, and an Atkin–Lehner matrix `W_Q`
for an exact divisor `Q ∥ N` normalises `Γ₀(N)`. Their determinants are `N`, respectively `Q`,
so for `N ≠ 1`, respectively `Q ≠ 1`, they do not lie in `SL₂(ℤ)`. Slashing both arguments of
the Petersson product by such a matrix of determinant `D` multiplies the product by `D ^ (k - 2)`
(`TauCeti.CuspForm.peterssonInnerCosets_slash_of_inv_conjAct_eq`), and the arithmetic
normalization `𝒲_Q = (√Q) ^ (2 - k) • (· ∣[k] W_Q)` is exactly the one that cancels this factor:
the normalizer is real and its square is `Q ^ (2 - k)`. So the normalized operators are
**unitary** for the Petersson product,

```text
⟪𝒲_N f, 𝒲_N g⟫ = ⟪f, g⟫   on S_k(Γ₁(N)),        ⟪𝒲_Q f, 𝒲_Q g⟫ = ⟪f, g⟫   on S_k(Γ₀(N)).
```

Combined with the square laws `𝒲_N² = (-1) ^ k` and `𝒲_Q² = 1`, unitarity gives the adjoints:
`𝒲_Q` is **self-adjoint** on `S_k(Γ₀(N))`, and `𝒲_N` is self-adjoint up to the sign `(-1) ^ k`
on `S_k(Γ₁(N))`. Consequently the Petersson-orthogonal complement of a subspace stable under one
of these operators is again stable under it. That is the form in which the Fricke and
Atkin–Lehner operators reach the newforms: the new subspace is the Petersson-orthogonal complement
of the old subspace, so an operator preserving the old subspace preserves the new one, and on a
newform of trivial nebentypus multiplicity one then turns `𝒲_Q f` into a multiple `± f` — the
Atkin–Lehner sign.

## Main results

* `TauCeti.peterssonInnerCosets_frickeOperatorCusp`: the raw Fricke operator scales the
  Petersson product by `N ^ (k - 2)`.
* `TauCeti.peterssonInnerCosets_normalizedFrickeOperatorCusp`: `𝒲_N` is unitary.
* `TauCeti.peterssonInnerCosets_normalizedFrickeOperatorCusp_left`: its adjoint is
  `(-1) ^ k • 𝒲_N`.
* `TauCeti.normalizedFrickeOperatorCusp_mem_peterssonOrthogonal`: the orthogonal
  complement of a `𝒲_N`-stable subspace is `𝒲_N`-stable.
* `TauCeti.Nat.IsExactDivisor.peterssonInnerCosets_atkinLehnerOperatorCusp`: the raw
  Atkin–Lehner operator scales the Petersson product by `Q ^ (k - 2)`.
* `TauCeti.Nat.IsExactDivisor.peterssonInnerCosets_normalizedAtkinLehnerOperatorCusp`: `𝒲_Q` is
  unitary.
* `TauCeti.Nat.IsExactDivisor.peterssonInnerCosets_normalizedAtkinLehnerOperatorCusp_left`:
  `𝒲_Q` is self-adjoint.
* `TauCeti.Nat.IsExactDivisor.normalizedAtkinLehnerOperatorCusp_mem_peterssonOrthogonal`: the
  orthogonal complement of a `𝒲_Q`-stable subspace is `𝒲_Q`-stable.

## References

* [F. Diamond and J. Shurman, *A First Course in Modular Forms*][diamondshurman2005], §5.5 and
  §5.10.
* Miyake, *Modular forms*, Sections 4.5 and 4.6.
* A. O. L. Atkin and J. Lehner, *Hecke operators on `Γ₀(m)`*, Math. Ann. 185 (1970), 134–160.
-/

public section

open Matrix.SpecialLinearGroup CongruenceSubgroup

open scoped MatrixGroups ModularForm ComplexConjugate TauCeti.ExactDivisor

namespace TauCeti

open _root_.CuspForm TauCeti.CuspForm

section Fricke

variable {N : ℕ} [NeZero N]

/-! ### The Fricke operator -/

/-- **The raw Fricke operator scales the Petersson product by `N ^ (k - 2)`**:
`⟪f ∣[k] W_N, g ∣[k] W_N⟫ = N ^ (k - 2) · ⟪f, g⟫` on `S_k(Γ₁(N))`, the determinant of
`W_N = !![0, -1; N, 0]` being `N`. -/
theorem peterssonInnerCosets_frickeOperatorCusp (k : ℤ)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    peterssonInnerCosets (frickeOperatorCusp k f) (frickeOperatorCusp k g) =
      (N : ℂ) ^ (k - 2) * peterssonInnerCosets f g := by
  rw [peterssonInnerCosets_slash_of_inv_conjAct_eq val_det_frickeGL_pos
    Gamma1_map_inv_conjAct_frickeGL_eq (coe_frickeOperatorCusp f) (coe_frickeOperatorCusp g),
    ← Matrix.GeneralLinearGroup.val_det_apply, val_det_frickeGL, Complex.ofReal_natCast]

/-- **The normalized Fricke operator is Petersson-unitary**: `⟪𝒲_N f, 𝒲_N g⟫ = ⟪f, g⟫` on
`S_k(Γ₁(N))`, in every weight. The normalizer `(√N) ^ (2 - k)` is real, so it contributes its
square `N ^ (2 - k)`, cancelling the factor `N ^ (k - 2)` of the raw operator. -/
@[simp]
theorem peterssonInnerCosets_normalizedFrickeOperatorCusp (k : ℤ)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    peterssonInnerCosets (normalizedFrickeOperatorCusp k f) (normalizedFrickeOperatorCusp k g) =
      peterssonInnerCosets f g := by
  rw [normalizedFrickeOperatorCusp_def, LinearMap.smul_apply, LinearMap.smul_apply,
    peterssonInnerCosets_smul_left, peterssonInnerCosets_smul_right,
    peterssonInnerCosets_frickeOperatorCusp, conj_atkinLehnerNormalizer, ← mul_assoc,
    ← mul_assoc, ← pow_two, atkinLehnerNormalizer_sq_mul (NeZero.ne N), one_mul]

/-- **The Petersson adjoint of the normalized Fricke operator** is `(-1) ^ k • 𝒲_N`:
`⟪𝒲_N f, g⟫ = (-1) ^ k · ⟪f, 𝒲_N g⟫` on `S_k(Γ₁(N))`. Unitarity and the square law
`𝒲_N² = (-1) ^ k` combine to this; in even weight `𝒲_N` is self-adjoint. -/
theorem peterssonInnerCosets_normalizedFrickeOperatorCusp_left (k : ℤ)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    peterssonInnerCosets (normalizedFrickeOperatorCusp k f) g =
      (-1 : ℂ) ^ k * peterssonInnerCosets f (normalizedFrickeOperatorCusp k g) := by
  -- write `g` as `𝒲_N ((-1) ^ k • 𝒲_N g)` and use unitarity
  have hg : normalizedFrickeOperatorCusp k ((-1 : ℂ) ^ k • normalizedFrickeOperatorCusp k g) =
      g := by
    rw [map_smul, normalizedFrickeOperatorCusp_normalizedFrickeOperatorCusp_apply, smul_smul,
      ← mul_zpow, neg_one_mul, neg_neg, one_zpow, one_smul]
  conv_lhs => rw [← hg]
  rw [peterssonInnerCosets_normalizedFrickeOperatorCusp, peterssonInnerCosets_smul_right]

/-- **The Petersson-orthogonal complement of a `𝒲_N`-stable subspace is `𝒲_N`-stable.** The
adjoint of `𝒲_N` is a scalar multiple of `𝒲_N` itself
(`peterssonInnerCosets_normalizedFrickeOperatorCusp_left`), so it preserves `V` whenever `𝒲_N`
does. -/
theorem normalizedFrickeOperatorCusp_mem_peterssonOrthogonal {k : ℤ}
    {V : Submodule ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k)}
    (hV : ∀ f ∈ V, normalizedFrickeOperatorCusp k f ∈ V)
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ peterssonOrthogonal V) :
    normalizedFrickeOperatorCusp k f ∈ peterssonOrthogonal V :=
  map_mem_peterssonOrthogonal (S := fun g ↦ (-1 : ℂ) ^ k • normalizedFrickeOperatorCusp k g)
    (fun f g ↦ by rw [peterssonInnerCosets_normalizedFrickeOperatorCusp_left,
      peterssonInnerCosets_smul_right])
    (fun g hg ↦ V.smul_mem _ (hV g hg)) hf

end Fricke

/-! ### The Atkin–Lehner operators -/

namespace Nat.IsExactDivisor

variable {N Q : ℕ} [NeZero N]

/-- **The raw Atkin–Lehner operator scales the Petersson product by `Q ^ (k - 2)`**:
`⟪f ∣[k] W_Q, g ∣[k] W_Q⟫ = Q ^ (k - 2) · ⟪f, g⟫` on `S_k(Γ₀(N))`, the determinant of an
Atkin–Lehner matrix for `Q` being `Q`. -/
theorem peterssonInnerCosets_atkinLehnerOperatorCusp (h : Q ∥ N) (k : ℤ)
    (f g : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :
    peterssonInnerCosets (h.atkinLehnerOperatorCusp k f) (h.atkinLehnerOperatorCusp k g) =
      (Q : ℂ) ^ (k - 2) * peterssonInnerCosets f g := by
  rw [CuspForm.peterssonInnerCosets_slash_of_inv_conjAct_eq (val_det_atkinLehnerGL_pos _ _)
      (Gamma0_map_inv_conjAct_atkinLehnerGL_eq h.pos h.dvd _)
      (h.coe_atkinLehnerOperatorCusp f) (h.coe_atkinLehnerOperatorCusp g),
    ← Matrix.GeneralLinearGroup.val_det_apply, val_det_atkinLehnerGL, Complex.ofReal_natCast]

/-- **The normalized Atkin–Lehner operator is Petersson-unitary**: `⟪𝒲_Q f, 𝒲_Q g⟫ = ⟪f, g⟫` on
`S_k(Γ₀(N))`. The real normalizer `(√Q) ^ (2 - k)` cancels the factor `Q ^ (k - 2)` of the raw
operator. -/
@[simp]
theorem peterssonInnerCosets_normalizedAtkinLehnerOperatorCusp (h : Q ∥ N) (k : ℤ)
    (f g : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :
    peterssonInnerCosets (h.normalizedAtkinLehnerOperatorCusp k f)
      (h.normalizedAtkinLehnerOperatorCusp k g) = peterssonInnerCosets f g := by
  rw [normalizedAtkinLehnerOperatorCusp_def, LinearMap.smul_apply, LinearMap.smul_apply,
    peterssonInnerCosets_smul_left, peterssonInnerCosets_smul_right,
    h.peterssonInnerCosets_atkinLehnerOperatorCusp, conj_atkinLehnerNormalizer, ← mul_assoc,
    ← mul_assoc, ← pow_two, atkinLehnerNormalizer_sq_mul h.ne_zero, one_mul]

/-- **The normalized Atkin–Lehner operator is Petersson self-adjoint**:
`⟪𝒲_Q f, g⟫ = ⟪f, 𝒲_Q g⟫` on `S_k(Γ₀(N))`, a unitary involution being its own adjoint. -/
theorem peterssonInnerCosets_normalizedAtkinLehnerOperatorCusp_left (h : Q ∥ N) (k : ℤ)
    (f g : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :
    peterssonInnerCosets (h.normalizedAtkinLehnerOperatorCusp k f) g =
      peterssonInnerCosets f (h.normalizedAtkinLehnerOperatorCusp k g) := by
  conv_lhs => rw [← h.normalizedAtkinLehnerOperatorCusp_normalizedAtkinLehnerOperatorCusp_self k g]
  exact h.peterssonInnerCosets_normalizedAtkinLehnerOperatorCusp k f _

/-- **The Petersson-orthogonal complement of a `𝒲_Q`-stable subspace is `𝒲_Q`-stable**, `𝒲_Q`
being self-adjoint. -/
theorem normalizedAtkinLehnerOperatorCusp_mem_peterssonOrthogonal (h : Q ∥ N) {k : ℤ}
    {V : Submodule ℂ (CuspForm ((Gamma0 N).map (mapGL ℝ)) k)}
    (hV : ∀ f ∈ V, h.normalizedAtkinLehnerOperatorCusp k f ∈ V)
    {f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k} (hf : f ∈ CuspForm.peterssonOrthogonal V) :
    h.normalizedAtkinLehnerOperatorCusp k f ∈ CuspForm.peterssonOrthogonal V :=
  CuspForm.map_mem_peterssonOrthogonal
    (h.peterssonInnerCosets_normalizedAtkinLehnerOperatorCusp_left k) hV hf

end Nat.IsExactDivisor

end TauCeti
