/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.HeckeRing.GL2.Gamma1.CoprimeCosets
import Mathlib.Data.Nat.Prime.Int

/-!
# The double coset of `diag(1, p)` is stable under conjugation by `Γ₀(N)`

The diamond operators act on `M_k(Γ₁(N))` through `Γ₀(N) ⧸ Γ₁(N)`, and they commute with `Tₚ`.
On the Hecke-ring side that commutation is not an analytic fact but a statement about double
cosets. The diamond `⟨d⟩` is the basis element of `Γ₁(N) · g · Γ₁(N)` for a `g ∈ Γ₀(N)`, and such
a `g` normalizes `Γ₁(N)`, so products taken with it carry no structure constant
(`HeckeCosetModule.single_mul_single_of_mem_normalizer`, and
`single_diamondCosetGamma1_mul_single_diamondCosetGamma1` for the diamonds among themselves).
Commuting `⟨d⟩` past the basis element of `Γ₁(N) · diag(1, p) · Γ₁(N)` therefore comes down to one
equation between double cosets,

`Γ₁(N) · (g · diag(1, p)) · Γ₁(N) = Γ₁(N) · (diag(1, p) · g) · Γ₁(N)`,

which — `g` normalizing `Γ₁(N)`, so that a `Γ₁(N)` factor may be moved across it — is exactly the
assertion that conjugating `diag(1, p)` by `g` does not leave the double coset. This file proves
that assertion, for `p` prime.

## The two branches, and why neither covers the other

Write `g = !![a, b; c, e] ∈ Γ₀(N)`, so `N ∣ c` and `a e − b c = 1`. The conjugate is

`g · diag(1, p) · g⁻¹ = !![1 + b c (1 − p), a b (p − 1); c e (1 − p), p + b c (p − 1)]`,

and membership in the double coset means writing it as `τ · diag(1, p) · γ` with `τ, γ ∈ Γ₁(N)`.

* **`e` coprime to `p`.** The right factor can be taken to be a power of `T = !![1, 1; 0, 1]`:
  the congruence `p ∣ b + j e` is solvable because `e` is invertible modulo `p`, and then
  `τ = C · (diag(1, p) · Tʲ)⁻¹` is integral of determinant one and satisfies the `Γ₁(N)`
  congruences, because `N ∣ c` makes the whole lower row divisible by `N`.
* **`p ∣ e`.** No power of `T` can work, so this is not a gap in the first argument: `p ∣ e`
  together with `a e − b c = 1` forces `b c ≡ −1 (mod p)`, hence `p ∤ b` once `1 < p`, while
  `p ∣ b + j e` reduces to `p ∣ b`. What happens instead is that the conjugate's first *column*
  becomes
  divisible by `p` — writing `e = p f`, the `(0, 0)` entry is `a e − b c p = p (a f − b c)` — so
  the conjugate factors as `τ′ · diag(1, p) · γ` with `γ = !![a f p, b c′; N, 1] ∈ Γ₁(N)`, writing
  `c = N c′`. The product `diag(1, p) · γ` is then the *twisted* representative `σ · diag(p, 1)`
  rather than an upper-triangular one.

The coprime branch reads its offset straight off a Bézout pair for `e` and `p`, and both outer
factors land in `Γ₁(N)` — the left one because `N ∣ c` makes the whole lower row divisible by `N`,
the right one because every power of `T` lies in `Γ₁(N)`.

At a prime the two branches are exhaustive, which is `conj_natDiagGL_mem_doubleCoset_of_prime`.
Neither needs `p` to be prime on its own, and neither needs a coprimality hypothesis relating
`p` to `N`: reducing `a (p f) − b c = 1` along `N ∣ c` leaves `(a f) p ≡ 1 (mod N)`, so `p` is
automatically invertible modulo the level wherever the twisted branch needs it.

## Main results

* `HeckeRing.GL2.conj_natDiagGL_mem_doubleCoset_of_isCoprime`: the coprime branch.
* `HeckeRing.GL2.conj_natDiagGL_mem_doubleCoset_of_dvd`: the branch where `p` divides the
  lower-right entry of the conjugating matrix.
* `HeckeRing.GL2.conj_natDiagGL_mem_doubleCoset_of_prime`: the two combined, at a prime.

## Provenance

No code is transcribed, and the statement has no counterpart to port. The AINTLIB
`LeanModularForms` project (Chris Birkbeck, Apache-2.0, commit
`6d87d596a5372d5b122c47b7082d4c3afa9b7c3b`) proves the diamond/Hecke commutation twice, but
never on the coset side: `HeckeRing.GL2.heckeT_n_comm_diamondOp`
(`HeckeRIngs/GL2/Unified/RingTransport.lean:298`) argues on the character eigenspace, where the
diamond is the scalar `χ(d)` and commutation is automatic, and `heckeT_p_comm_diamondOp`
(`HeckeRIngs/GL2/HeckeT_p.lean:983`) is an operator-level slash identity. Both take the analytic
action as given; the double-coset statement below is what a Hecke *ring* needs, and is proved
here from the group law and the matrix entries.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005], §5.2.
* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.4–3.5.
-/

public section

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup DoubleCoset HeckeRing.GLn

open scoped MatrixGroups Pointwise

namespace HeckeRing.GL2

variable {N p : ℕ}

/-- The matrix of `diag(1, p)` as the image of an integer matrix, the shape the integral-witness
API consumes. Derived from `coe_natDiagGL_one`, which is where this matrix is stated, rather than
from the rank-`n` `HeckeRing.GLn.natDiagGL_coe_eq_map_intCast`: either route works, and this one
keeps a single source for the matrix of `diag(1, p)`. -/
private lemma coe_natDiagGL_one_eq_map (hp : 0 < p) :
    ((natDiagGL 2 ![1, p] : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ)
      = (!![1, 0; 0, (p : ℤ)] : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℚ) := by
  rw [coe_natDiagGL_one hp]
  ext i k
  fin_cases i <;> fin_cases k <;> simp

/-- The conjugate `g · diag(1, p) · g⁻¹` of the diagonal matrix by `g = !![a, b; c, e]`, for
`g` of determinant one, written out. -/
private def conjDiag (a b c e p : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![1 + b * c * (1 - p), a * b * (p - 1); c * e * (1 - p), p + b * c * (p - 1)]

/-- **`conjDiag` is what the triple product is**, by `!![a, b; c, e]⁻¹ = !![e, -b; -c, a]`. -/
private lemma conjDiag_eq (a b c e p : ℤ) (hdet : a * e - b * c = 1) :
    (!![a, b; c, e] * !![1, 0; 0, p] * !![e, -b; -c, a] : Matrix (Fin 2) (Fin 2) ℤ) =
      conjDiag a b c e p := by
  ext i k
  fin_cases i <;> fin_cases k <;> simp [conjDiag, Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination hdet
  · ring
  · ring
  · linear_combination p * hdet

/-- **The conjugate is the integer matrix `conjDiag`**, cast into `ℚ`. -/
private lemma coe_conj_natDiagGL (hp : 0 < p) (g : SL(2, ℤ)) :
    ((mapGL ℚ g * natDiagGL 2 ![1, p] * mapGL ℚ g⁻¹ : GL (Fin 2) ℚ) :
        Matrix (Fin 2) (Fin 2) ℚ)
      = (conjDiag (g 0 0) (g 0 1) (g 1 0) (g 1 1) (p : ℤ)).map (Int.cast : ℤ → ℚ) := by
  have hginv : ((g⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
      = !![g 1 1, -(g 0 1); -(g 1 0), g 0 0] := by
    rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
    rfl
  rw [mapGL_mul_coe_eq_intMatrix 2 g g⁻¹ _ _ (coe_natDiagGL_one_eq_map hp),
    Matrix.eta_fin_two ((g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ), hginv,
    conjDiag_eq _ _ _ _ _ (Matrix.SpecialLinearGroup.fin_two_mul_sub_mul_eq_one g)]
  simp

/-- The `Γ₁` factor of the coprime branch: `conjDiag · (diag(1, p) · Tʲ)⁻¹`, at an offset with
`b + j e = p t`. -/
private def conjTau (a b c e p j t : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![1 + b * c * (1 - p), a * b + j * (b * c) - a * t;
     c * e * (1 - p), 1 + b * c + j * c * e - c * t]

/-- **`τ · (diag(1, p) · Tʲ) = C`**; the offset hypothesis is what clears the `(0,1)` entry. -/
private lemma conjTau_mul (a b c e p j t : ℤ) (hdet : a * e - b * c = 1)
    (ht : b + j * e = p * t) :
    (conjTau a b c e p j t * !![1, j; 0, p] : Matrix (Fin 2) (Fin 2) ℤ) =
      conjDiag a b c e p := by
  ext i k
  fin_cases i <;> fin_cases k <;>
    simp [conjTau, conjDiag, Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination (-j) * hdet + a * ht
  · linear_combination c * ht

/-- **`det τ = 1`**, by expanding against `a e - b c = 1` and `b + j e = p t`. -/
private lemma conjTau_det (a b c e p j t : ℤ) (hdet : a * e - b * c = 1) (ht : b + j * e = p * t) :
    (conjTau a b c e p j t).det = 1 := by
  rw [conjTau, Matrix.det_fin_two_of]
  linear_combination (c * (1 - p) * (t - b)) * hdet + c * ht

/-- **`τ` satisfies the `Γ₁(N)` congruences on its lower row**, both because that row carries a
factor of `c`, which `Γ₀(N)` membership makes divisible by `N`. -/
private lemma conjTau_gamma1 (a b c e p j t : ℤ) (hc : (N : ℤ) ∣ c) :
    (N : ℤ) ∣ conjTau a b c e p j t 1 0 ∧ (N : ℤ) ∣ conjTau a b c e p j t 1 1 - 1 := by
  obtain ⟨d, rfl⟩ := hc
  exact ⟨⟨d * e * (1 - p), by simp [conjTau]; ring⟩,
    ⟨b * d + j * d * e - d * t, by simp [conjTau]; ring⟩⟩

/-- **The coprime branch, at the level of integer matrices.** A Bézout pair `u e + v p = 1`
hands over the offset `j = -b u` outright — no division is needed, since `b + j e = p (b v)`
follows by multiplying the relation by `b`. -/
private lemma exists_mem_Gamma1_mul_diag_mul_eq_conjDiag_of_bezout {a b c e u v : ℤ}
    (hdet : a * e - b * c = 1) (hc : (N : ℤ) ∣ c) (huv : u * e + v * (p : ℤ) = 1) :
    ∃ τ ∈ Gamma1 N, ∃ γ ∈ Gamma1 N, (τ : Matrix (Fin 2) (Fin 2) ℤ) *
      !![1, 0; 0, (p : ℤ)] * (γ : Matrix (Fin 2) (Fin 2) ℤ) = conjDiag a b c e (p : ℤ) := by
  have ht : b + (-b * u) * e = (p : ℤ) * (b * v) := by linear_combination (-b) * huv
  refine ⟨⟨_, conjTau_det _ _ _ _ _ _ _ hdet ht⟩,
    mem_Gamma1_iff_dvd_lowerRow.mpr <| conjTau_gamma1 _ _ _ _ _ _ _ hc, ModularGroup.T ^ (-b * u),
    T_zpow_mem_Gamma1 N _, ?_⟩
  rw [ModularGroup.coe_T_zpow, mul_assoc, Matrix.mul_fin_two]
  simp only [mul_one, one_mul, mul_zero, zero_mul, add_zero, zero_add]
  exact conjTau_mul _ _ _ _ _ _ _ hdet ht

/-- **Conjugation by `Γ₀(N)` fixes the double coset of `diag(1, p)`**, when the lower-right
entry of the conjugating matrix is coprime to `p`. The complementary case, where `p` divides
that entry, is `conj_natDiagGL_mem_doubleCoset_of_dvd`. -/
theorem conj_natDiagGL_mem_doubleCoset_of_isCoprime (hp : 0 < p) {g : SL(2, ℤ)} (hg : g ∈ Gamma0 N)
    (hco : IsCoprime (g 1 1) (p : ℤ)) :
    mapGL ℚ g * natDiagGL 2 ![1, p] * mapGL ℚ g⁻¹ ∈ doubleCoset (natDiagGL 2 ![1, p] : GL (Fin 2) ℚ)
      ((Gamma1 N).map (mapGL ℚ)) ((Gamma1 N).map (mapGL ℚ)) := by
  obtain ⟨u, v, huv⟩ := hco
  obtain ⟨τ, hτ, γ, hγ, h⟩ := exists_mem_Gamma1_mul_diag_mul_eq_conjDiag_of_bezout
    g.fin_two_mul_sub_mul_eq_one (mem_Gamma0_iff_dvd.mp hg) huv
  exact mem_doubleCoset_of_intMatrix_eq_of_mem 2 τ γ (Subgroup.mem_map_of_mem _ hτ)
    (Subgroup.mem_map_of_mem _ hγ) _ _ _ _ (coe_natDiagGL_one_eq_map hp) (coe_conj_natDiagGL hp g) h

/-- **The twisted `Γ₁` factor, parametrized by the conjugate's entries.** If the conjugate is
`!![p α, β; p γ, δ]` — i.e. its first column is divisible by `p`, which is what `p ∣ e` gives —
then this is `C · (σ · diag(p, 1))⁻¹` for `σ = !![m, n; N, p]`.

Stated in `α, β, γ, δ` rather than in `a, b, c, f` so that it composes with whatever expression
the conjugate is presented as. -/
private def twistTau (p α β γ δ m n N : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![p * α - β * N, -α * n + β * m; p * γ - δ * N, -γ * n + δ * m]

/-- **`τ′ · (σ · diag(p, 1)) = C`**, one `linear_combination` per entry against `m p - n N = 1`. -/
private lemma twistTau_mul (p α β γ δ m n N : ℤ) (hσ : m * p - n * N = 1) :
    (twistTau p α β γ δ m n N * !![m * p, n; N * p, p] : Matrix (Fin 2) (Fin 2) ℤ)
      = !![p * α, β; p * γ, δ] := by
  ext i k
  fin_cases i <;> fin_cases k <;> simp [twistTau, Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination (p * α) * hσ
  · linear_combination β * hσ
  · linear_combination (p * γ) * hσ
  · linear_combination δ * hσ

/-- **`det τ′ = 1`**, since `det τ′ = (α δ - β γ) (m p - n N)`. -/
private lemma twistTau_det (p α β γ δ m n N : ℤ) (hσ : m * p - n * N = 1)
    (hαδ : α * δ - β * γ = 1) : (twistTau p α β γ δ m n N).det = 1 := by
  rw [twistTau, Matrix.det_fin_two_of]
  linear_combination (α * δ - β * γ) * hσ + hαδ

/-- **`τ′` satisfies the `Γ₁(N)` congruences on its lower row.** The two hypotheses are what the
concrete conjugate supplies — `N ∣ γ` and `δ ≡ p`, both because the conjugate's lower row carries
a factor of `c`. The `(1, 1)` entry additionally needs `m p ≡ 1 (mod N)`, which is `hσ` reduced. -/
private lemma twistTau_gamma1 (p α β γ δ m n : ℤ) (hγ : (N : ℤ) ∣ γ) (hδ : (N : ℤ) ∣ δ - p)
    (hσ : m * p - n * (N : ℤ) = 1) :
    (N : ℤ) ∣ twistTau p α β γ δ m n (N : ℤ) 1 0 ∧
      (N : ℤ) ∣ twistTau p α β γ δ m n (N : ℤ) 1 1 - 1 := by
  obtain ⟨v, rfl⟩ := hγ
  obtain ⟨w, hw⟩ := hδ
  exact ⟨⟨p * v - δ, by simp [twistTau]; ring⟩,
    ⟨-v * n + n + w * m, by simp [twistTau]; linear_combination m * hw + hσ⟩⟩

/-- **The conjugate, in the `p ∣ e` parametrisation.** Writing `e = p f`, the conjugate matrix
`!![1 + bc(1-p), ab(p-1); ce(1-p), p + bc(p-1)]` has its first column divisible by `p`, with
quotients `α = a f - b c` and `γ = c f (1 - p)` — the `(0, 0)` entry because `1 + b c = a e` by
the determinant relation, so the entry is `a e - b c p`. -/
private lemma conjDiag_eq_twisted (a b c f p : ℤ) (hdet : a * (p * f) - b * c = 1) :
    conjDiag a b c (p * f) p
      = !![p * (a * f - b * c), a * b * (p - 1);
           p * (c * f * (1 - p)), p + b * c * (p - 1)] := by
  rw [conjDiag]
  ext i k
  fin_cases i <;> fin_cases k <;> simp
  · linear_combination -hdet
  · ring

/-- **The twisted representative is an integer matrix**, cast into `ℚ` — the shape
`eq_mapGL_mul_mul_mapGL_of_intMatrix_eq` consumes. Only a change of shape on top of
`CoprimeCosets`' `coe_primeRep_none`. -/
private lemma coe_primeRep_none_eq_map (hp : 0 < p) (σ : SL(2, ℤ)) :
    ((primeRep σ p none : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ)
      = (!![σ 0 0 * (p : ℤ), σ 0 1; σ 1 0 * (p : ℤ), σ 1 1] :
          Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℚ) := by
  rw [coe_primeRep_none hp]
  ext i k
  fin_cases i <;> fin_cases k <;> simp

/-- **The twisted branch, at the level of integer matrices.** A Bézout relation
`a f p − b c′ N = 1` supplies a `τ′ ∈ Γ₁(N)` carrying the matrix of the last right coset's
twisted representative — `σ · diag(p, 1)` for `σ` with bottom row `(N, p)` — onto
`conjDiag a b (N c′) (p f) p`.

Only the left factor is built here. The right one is `CoprimeCosets`' own: at that bottom row
`exists_mem_Gamma1_natDiagGL_mul_eq_primeRep_none` already produces a `γ ∈ Γ₁(N)` with
`diag(1, p) · γ = primeRep σ p none`, so there is nothing to re-derive. -/
private lemma exists_mem_Gamma1_mul_twistedRep_eq_conjDiag_of_bezout {a b c' f : ℤ}
    (hσ : a * f * (p : ℤ) - b * c' * (N : ℤ) = 1) :
    ∃ τ ∈ Gamma1 N, (τ : Matrix (Fin 2) (Fin 2) ℤ) *
      !![a * f * (p : ℤ), b * c'; (N : ℤ) * (p : ℤ), (p : ℤ)] =
        conjDiag a b ((N : ℤ) * c') ((p : ℤ) * f) (p : ℤ) := by
  -- the conjugate's entries, in the form `!![p α, β; p γ, δ]`
  have hconj := conjDiag_eq_twisted a b ((N : ℤ) * c') f (p : ℤ) (by linear_combination hσ)
  -- the left factor `τ′`, with `α, β, γ, δ` read off `hconj`
  refine ⟨⟨_, twistTau_det _ _ _ _ _ _ _ _ hσ ?_⟩,
    mem_Gamma1_iff_dvd_lowerRow.mpr <| twistTau_gamma1 _ _ _ _ _ _ _ ?_ ?_ hσ,
    (twistTau_mul _ _ _ _ _ _ _ _ hσ).trans hconj.symm⟩
  · linear_combination (1 + b * ((N : ℤ) * c') * ((p : ℤ) - 1)) * hσ
  · exact ((dvd_mul_right _ _).mul_right _).mul_right _
  · rw [add_sub_cancel_left]
    exact ((dvd_mul_right _ _).mul_left _).mul_right _

/-- **Conjugation by `Γ₀(N)` fixes the double coset of `diag(1, p)`**, when `p` divides the
lower-right entry of the conjugating matrix. The complementary case, where that entry is coprime to
`p`, is `conj_natDiagGL_mem_doubleCoset_of_isCoprime`. -/
theorem conj_natDiagGL_mem_doubleCoset_of_dvd (hp : 0 < p) {g : SL(2, ℤ)} (hg : g ∈ Gamma0 N)
    (he : (p : ℤ) ∣ g 1 1) :
    mapGL ℚ g * natDiagGL 2 ![1, p] * mapGL ℚ g⁻¹ ∈ doubleCoset (natDiagGL 2 ![1, p] : GL (Fin 2) ℚ)
      ((Gamma1 N).map (mapGL ℚ)) ((Gamma1 N).map (mapGL ℚ)) := by
  obtain ⟨f, hf⟩ := he
  obtain ⟨c', hc'⟩ := mem_Gamma0_iff_dvd.mp hg
  have hσ : g 0 0 * f * (p : ℤ) - g 0 1 * c' * (N : ℤ) = 1 := by
    linear_combination g.fin_two_mul_sub_mul_eq_one - g 0 0 * hf + g 0 1 * hc'
  -- the last right coset's twisted representative, with bottom row `(N, p)`
  let σ : SL(2, ℤ) := ⟨!![g 0 0 * f, g 0 1 * c'; N, p], (Matrix.det_fin_two_of _ _ _ _).trans hσ⟩
  obtain ⟨γ, hγ, hγeq⟩ := exists_mem_Gamma1_natDiagGL_mul_eq_primeRep_none (σ := σ) hp rfl rfl
  obtain ⟨τ, hτ, hτeq⟩ := exists_mem_Gamma1_mul_twistedRep_eq_conjDiag_of_bezout hσ
  refine mem_doubleCoset.mpr ⟨_, Subgroup.mem_map_of_mem _ hτ, _, Subgroup.mem_map_of_mem _ hγ, ?_⟩
  rw [mul_assoc (mapGL ℚ τ), hγeq]
  exact (eq_mapGL_mul_mul_mapGL_of_intMatrix_eq 2 τ 1 _ _ _ _ (coe_primeRep_none_eq_map hp σ)
    (coe_conj_natDiagGL hp g) (by rwa [hc', hf, coe_one, mul_one])).trans (by rw [map_one, mul_one])

/-- **The `Γ₁(N)` double coset of `diag(1, p)` is stable under conjugation by `Γ₀(N)`**, for `p`
prime.

Combines `conj_natDiagGL_mem_doubleCoset_of_dvd` and
`conj_natDiagGL_mem_doubleCoset_of_isCoprime`, which between them cover every case at a prime. -/
theorem conj_natDiagGL_mem_doubleCoset_of_prime (hp : p.Prime) {g : SL(2, ℤ)} (hg : g ∈ Gamma0 N) :
    mapGL ℚ g * natDiagGL 2 ![1, p] * mapGL ℚ g⁻¹ ∈ doubleCoset (natDiagGL 2 ![1, p] : GL (Fin 2) ℚ)
      ((Gamma1 N).map (mapGL ℚ)) ((Gamma1 N).map (mapGL ℚ)) := by
  by_cases he : (p : ℤ) ∣ g 1 1
  · exact conj_natDiagGL_mem_doubleCoset_of_dvd hp.pos hg he
  · exact conj_natDiagGL_mem_doubleCoset_of_isCoprime hp.pos hg
      ((Nat.prime_iff_prime_int.mp hp).coprime_iff_not_dvd.mpr he).symm

end HeckeRing.GL2
