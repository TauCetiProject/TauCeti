/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Data.Rat.Defs
public import TauCeti.LowDimTopology.Plumbing.SpinC
public import TauCeti.LowDimTopology.Plumbing.Weight.Sublevel
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith
import TauCeti.LinearAlgebra.Matrix.Symmetric

/-!
# The rational square of a plumbing covector and the lattice correction term

Let `Q` be the intersection matrix of a plumbing graph `P` with vertex set `V`, and suppose that
`Q` is nonsingular, as it is for a negative-definite plumbing. The **square** of an integral
covector `k : V → ℤ` is the rational number

`k² = k · Q⁻¹ k`,

the self-pairing of the dual vector `Q⁻¹ k` (`TauCeti.PlumbingGraph.covectorSquare`). For the
plumbed four-manifold `X` with rational homology sphere boundary, a characteristic covector is the
first Chern class of a spin^c structure on `X`, and `k²` is its rational square `c₁²`. Writing
`Q⁻¹ = (det Q)⁻¹ adj Q` gives `k² = (k · adj Q k) / det Q`
(`TauCeti.PlumbingGraph.covectorSquare_eq_div_det`), so `det Q · k²` is an integer.

**Translation by `2 Q l`.** Since `Q⁻¹ Q = 1` and `Q` is symmetric, expanding the square gives

`(k + 2 Q l)² = k² + 4 (⟨k, l⟩ + Q(l, l))`

(`TauCeti.PlumbingGraph.covectorSquare_add_two_mulVec`). For a characteristic `k` the bracket is
`-2 χ_k(l)`, where `χ_k` is the characteristic weight function of lattice homology
(`TauCeti.PlumbingGraph.characteristicWeight`), so

`(k + 2 Q l)² = k² - 8 χ_k(l)`

(`TauCeti.PlumbingGraph.covectorSquare_add_two_mulVec_eq_sub`). This is Némethi's identity
relating the squares of the covectors of one spin^c orbit `[k] = k + 2 Q ℤ^V` to the weight
function.

**The maximal square in an orbit.** On a negative-definite plumbing the weight `χ_k` attains its
minimum `m_k` (`TauCeti.PlumbingGraph.sInfCharacteristicWeight`). By the identity above, the
largest square of a covector of `[k]` is `k² - 8 m_k`, attained at `k + 2 Q l` for a minimizer `l`
(`IsNegativeDefinite.isGreatest_covectorSquare`). The **lattice correction term**

`(k² + |V|) / 4 - 2 m_k`

(`TauCeti.PlumbingGraph.latticeCorrectionTerm`) is therefore the maximum of `(k'² + |V|) / 4` over
the orbit of `k` (`IsNegativeDefinite.isGreatest_latticeCorrectionTerm`). In particular it depends
only on the orbit (`IsNegativeDefinite.latticeCorrectionTerm_eq_of_isSpinCEquivalent`), and it is
unchanged by conjugation `k ↦ -k` (`TauCeti.PlumbingGraph.latticeCorrectionTerm_conjugate`).
These are the lattice-side normalizations of the grading of lattice homology. The maximum
`max_{k' ∈ [k]} (k'² + |V|) / 4` is the formula of Ozsváth and Szabó for the correction term of the
boundary three-manifold of a negative-definite plumbing with at most one bad vertex; that
identification belongs to Heegaard Floer theory and is not made here.

## Main definitions

* `TauCeti.PlumbingGraph.covectorSquare`: the rational square `k · Q⁻¹ k` of a covector.
* `TauCeti.PlumbingGraph.latticeCorrectionTerm`: the number `(k² + |V|) / 4 - 2 m_k`.

## Main results

* `TauCeti.PlumbingGraph.covectorSquare_eq_div_det`: `k² = (k · adj Q k) / det Q`.
* `TauCeti.PlumbingGraph.covectorSquare_add_two_mulVec`:
  `(k + 2 Q l)² = k² + 4 (⟨k, l⟩ + l · Q l)`.
* `TauCeti.PlumbingGraph.covectorSquare_add_two_mulVec_eq_sub`: `(k + 2 Q l)² = k² - 8 χ_k(l)`.
* `TauCeti.PlumbingGraph.IsNegativeDefinite.isGreatest_covectorSquare`: the largest square in
  the orbit of `k` is `k² - 8 m_k`.
* `TauCeti.PlumbingGraph.IsNegativeDefinite.isGreatest_latticeCorrectionTerm`: the lattice
  correction term is `max_{k' ∈ [k]} (k'² + |V|) / 4`.
* `TauCeti.PlumbingGraph.IsNegativeDefinite.latticeCorrectionTerm_eq_of_isSpinCEquivalent`: it
  is constant on spin^c orbits.

## References

* A. Némethi, *Lattice cohomology of normal surface singularities*,
  [arXiv:0709.0841](https://arxiv.org/abs/0709.0841), §2.2 and §3.3 (the identity
  `(k + 2l)² = k² - 8 χ_k(l)` and the normalization `(k_r² + |V|) / 4 - 2 m_{k_r}`).
* P. Ozsváth and Z. Szabó, *On the Floer homology of plumbed three-manifolds*, Geom. Topol. **7**
  (2003), [arXiv:math/0203265](https://arxiv.org/abs/math/0203265), Corollary 1.5 (the correction
  term as `max (K² + |V|) / 4`).
-/

public section

open Matrix

namespace TauCeti

namespace PlumbingGraph

variable {V : Type*} [DecidableEq V] [Fintype V] (P : PlumbingGraph V)

/-! ### The rational square of a covector -/

/-- The **rational square** `k² = k · Q⁻¹ k` of an integral covector `k`, where `Q⁻¹` is the
inverse of the intersection matrix over `ℚ`. It is the self-pairing of the rational dual vector
`Q⁻¹ k`. When `Q` is singular, `Q⁻¹ = 0` in Mathlib's convention and the square is `0`; the
results below assume `det Q ≠ 0`. -/
noncomputable def covectorSquare (k : V → ℤ) : ℚ :=
  (fun v => (k v : ℚ)) ⬝ᵥ ((P.intersectionMatrix.map ((↑) : ℤ → ℚ))⁻¹ *ᵥ fun v => (k v : ℚ))

/-- The rational square is `k · Q⁻¹ k`, with `Q⁻¹` the rational inverse of the intersection
matrix. -/
private theorem covectorSquare_def_aux (k : V → ℤ) :
    P.covectorSquare k =
      (fun v => (k v : ℚ)) ⬝ᵥ ((P.intersectionMatrix.map ((↑) : ℤ → ℚ))⁻¹ *ᵥ fun v => (k v : ℚ)) :=
  rfl

/-- The rational square is `k · Q⁻¹ k`, with `Q⁻¹` the rational inverse of the intersection
matrix. -/
theorem covectorSquare_def (k : V → ℤ) :
    P.covectorSquare k =
      (fun v => (k v : ℚ)) ⬝ᵥ ((P.intersectionMatrix.map ((↑) : ℤ → ℚ))⁻¹ *ᵥ fun v => (k v : ℚ)) :=
  covectorSquare_def_aux P k

/-- The zero covector has square zero. -/
@[simp]
theorem covectorSquare_zero : P.covectorSquare 0 = 0 := by
  simp [covectorSquare_def]

/-- The square is even: `(-k)² = k²`. -/
@[simp]
theorem covectorSquare_neg (k : V → ℤ) : P.covectorSquare (-k) = P.covectorSquare k := by
  have hneg : (fun v => ((-k) v : ℚ)) = -fun v => (k v : ℚ) := by
    ext v
    simp
  rw [covectorSquare_def, covectorSquare_def, hneg, mulVec_neg, neg_dotProduct, dotProduct_neg,
    neg_neg]

/-- The determinant of the rational intersection matrix is the cast of the integer determinant. -/
private theorem det_map_intCast :
    (P.intersectionMatrix.map ((↑) : ℤ → ℚ)).det = (P.intersectionMatrix.det : ℚ) :=
  ((Int.castRingHom ℚ).map_det P.intersectionMatrix).symm

/-- **The square through the adjugate.** `k² = (k · adj Q k) / det Q`. This equation needs no
nonsingularity, since both sides vanish when `det Q = 0`. When `det Q ≠ 0` it shows that
`det Q • k²` is the integer `k · adj Q k`. -/
theorem covectorSquare_eq_div_det (k : V → ℤ) :
    P.covectorSquare k =
      ((k ⬝ᵥ (P.intersectionMatrix.adjugate *ᵥ k) : ℤ) : ℚ) / P.intersectionMatrix.det := by
  have hadj : (P.intersectionMatrix.map ((↑) : ℤ → ℚ)).adjugate =
      P.intersectionMatrix.adjugate.map ((↑) : ℤ → ℚ) :=
    ((Int.castRingHom ℚ).map_adjugate P.intersectionMatrix).symm
  have hcast : ((k ⬝ᵥ (P.intersectionMatrix.adjugate *ᵥ k) : ℤ) : ℚ) =
      (fun v => (k v : ℚ)) ⬝ᵥ
        (P.intersectionMatrix.adjugate.map ((↑) : ℤ → ℚ) *ᵥ fun v => (k v : ℚ)) := by
    simp only [dotProduct, mulVec, map_apply, Int.cast_sum, Int.cast_mul]
  rw [covectorSquare_def, inv_def, hadj, det_map_intCast, hcast]
  simp [Ring.inverse_eq_inv', smul_mulVec, div_eq_inv_mul]

/-! ### Translation by twice the image of the intersection matrix -/

/-- The image under `Q` of an integral vector, cast to `ℚ`, is the image of the cast vector
under the rational intersection matrix. -/
private theorem cast_mulVec (l : V → ℤ) :
    (fun v => ((P.intersectionMatrix *ᵥ l) v : ℚ)) =
      P.intersectionMatrix.map ((↑) : ℤ → ℚ) *ᵥ fun v => (l v : ℚ) := by
  ext v
  exact (Int.castRingHom ℚ).map_mulVec P.intersectionMatrix l v

/-- The characteristic-weight numerator `⟨k, l⟩ + l · Q l`, cast to `ℚ`, in matrix form. -/
private theorem cast_characteristicWeightNumerator (k l : V → ℤ) :
    (P.characteristicWeightNumerator k l : ℚ) =
      (fun v => (k v : ℚ)) ⬝ᵥ (fun v => (l v : ℚ)) +
        (fun v => (l v : ℚ)) ⬝ᵥ
          (P.intersectionMatrix.map ((↑) : ℤ → ℚ) *ᵥ fun v => (l v : ℚ)) := by
  rw [characteristicWeightNumerator_def, intersectionForm_apply, ← cast_mulVec]
  simp only [dotProduct, mulVec, Finset.mul_sum, Int.cast_add, Int.cast_sum, Int.cast_mul,
    mul_assoc]

/-- **Translating a covector by `2 Q l`.** If the intersection matrix `Q` is nonsingular, then
`(k + 2 Q l)² = k² + 4 (⟨k, l⟩ + l · Q l)`, where the bracket is the characteristic-weight numerator
`characteristicWeightNumerator k l`. -/
theorem covectorSquare_add_two_mulVec (hQ : P.intersectionMatrix.det ≠ 0) (k l : V → ℤ) :
    P.covectorSquare (fun v => k v + 2 * (P.intersectionMatrix *ᵥ l) v) =
      P.covectorSquare k + 4 * P.characteristicWeightNumerator k l := by
  have hunit : IsUnit (P.intersectionMatrix.map ((↑) : ℤ → ℚ)).det := by
    rw [det_map_intCast]
    exact isUnit_iff_ne_zero.2 (by exact_mod_cast hQ)
  have hcast : (fun v => ((k v + 2 * (P.intersectionMatrix *ᵥ l) v : ℤ) : ℚ)) =
      (fun v => (k v : ℚ)) +
        P.intersectionMatrix.map ((↑) : ℤ → ℚ) *ᵥ (2 : ℚ) • fun v => (l v : ℚ) := by
    rw [mulVec_smul, ← cast_mulVec]
    ext v
    simp
  rw [covectorSquare_def, covectorSquare_def, hcast, cast_characteristicWeightNumerator,
    (P.intersectionMatrix_isSymm.map _).add_mulVec_dotProduct_inv_mulVec_add_mulVec hunit]
  simp only [dotProduct_smul, smul_dotProduct, mulVec_smul, smul_eq_mul]
  ring

/-- **Némethi's identity.** For a characteristic covector `k` and a nonsingular intersection
matrix `Q`, translating `k` by `2 Q l` lowers its square by eight times the characteristic weight
of `l`: `(k + 2 Q l)² = k² - 8 χ_k(l)`. -/
theorem covectorSquare_add_two_mulVec_eq_sub (hQ : P.intersectionMatrix.det ≠ 0)
    (k : P.characteristicVectors) (l : V → ℤ) :
    P.covectorSquare (fun v => k.val v + 2 * (P.intersectionMatrix *ᵥ l) v) =
      P.covectorSquare k.val - 8 * P.characteristicWeight k l := by
  have h2 : (P.characteristicWeightNumerator k.val l : ℚ) = -2 * P.characteristicWeight k l := by
    have := P.two_mul_characteristicWeight k l
    have hq : ((2 * P.characteristicWeight k l : ℤ) : ℚ) =
        ((-P.characteristicWeightNumerator k.val l : ℤ) : ℚ) := congrArg _ this
    push_cast at hq
    linarith
  rw [P.covectorSquare_add_two_mulVec hQ, h2]
  ring

/-- The squares of two covectors in the same spin^c orbit differ by eight times a characteristic
weight: if `k' = k + 2 Q l`, then `k'² = k² - 8 χ_k(l)`. -/
theorem IsSpinCEquivalent.exists_covectorSquare_eq_sub (hQ : P.intersectionMatrix.det ≠ 0)
    {k k' : P.characteristicVectors} (hk : P.IsSpinCEquivalent k k') :
    ∃ l : V → ℤ,
      P.covectorSquare k'.val = P.covectorSquare k.val - 8 * P.characteristicWeight k l := by
  obtain ⟨l, hl⟩ := (P.isSpinCEquivalent_iff k k').1 hk
  exact ⟨l, by rw [hl, P.covectorSquare_add_two_mulVec_eq_sub hQ]⟩

/-! ### The maximal square in a spin^c orbit -/

variable {P}

/-- **The largest square in a spin^c orbit.** On a negative-definite plumbing, the squares of the
characteristic covectors spin^c equivalent to `k` have the greatest element `k² - 8 m_k`, where
`m_k` is the minimum of the characteristic weight function `χ_k`. -/
theorem IsNegativeDefinite.isGreatest_covectorSquare (h : P.IsNegativeDefinite)
    (k : P.characteristicVectors) :
    IsGreatest {q : ℚ | ∃ k', P.IsSpinCEquivalent k k' ∧ q = P.covectorSquare k'.val}
      (P.covectorSquare k.val - 8 * P.sInfCharacteristicWeight k) := by
  have hQ := h.det_intersectionMatrix_ne_zero
  constructor
  · obtain ⟨l, hl⟩ := P.exists_characteristicWeight_eq_sInfCharacteristicWeight k
    refine ⟨⟨fun v => k.val v + 2 * (P.intersectionMatrix *ᵥ l) v,
      IsCharacteristicVector.add_two_mul P k.property⟩, (P.isSpinCEquivalent_iff _ _).2 ⟨l, rfl⟩,
      ?_⟩
    rw [P.covectorSquare_add_two_mulVec_eq_sub hQ, hl]
  · rintro q ⟨k', hk', rfl⟩
    obtain ⟨l, hl⟩ := hk'.exists_covectorSquare_eq_sub P hQ
    rw [hl]
    have hm : (P.sInfCharacteristicWeight k : ℚ) ≤ P.characteristicWeight k l := by
      exact_mod_cast P.sInfCharacteristicWeight_le h k l
    linarith

/-! ### The lattice correction term -/

variable (P) in
/-- The **lattice correction term** of a characteristic covector `k`:
`(k² + |V|) / 4 - 2 m_k`, where `k²` is the rational square `covectorSquare` and
`m_k = sInfCharacteristicWeight k` is the infimum of the characteristic weight function. On a
negative-definite plumbing `m_k` is a minimum, and the term is the maximum of `(k'² + |V|) / 4`
over the spin^c orbit of `k` (`IsNegativeDefinite.isGreatest_latticeCorrectionTerm`). Off that
domain the formula uses the junk values of `covectorSquare` (`0` when `Q` is singular) and of
`sInfCharacteristicWeight` (`0` when the weight is unbounded below). -/
noncomputable def latticeCorrectionTerm (k : P.characteristicVectors) : ℚ :=
  (P.covectorSquare k.val + Fintype.card V) / 4 - 2 * P.sInfCharacteristicWeight k

variable (P) in
/-- The lattice correction term is `(k² + |V|) / 4 - 2 m_k`. -/
private theorem latticeCorrectionTerm_def_aux (k : P.characteristicVectors) :
    P.latticeCorrectionTerm k =
      (P.covectorSquare k.val + Fintype.card V) / 4 - 2 * P.sInfCharacteristicWeight k :=
  rfl

variable (P) in
/-- The lattice correction term is `(k² + |V|) / 4 - 2 m_k`. -/
theorem latticeCorrectionTerm_def (k : P.characteristicVectors) :
    P.latticeCorrectionTerm k =
      (P.covectorSquare k.val + Fintype.card V) / 4 - 2 * P.sInfCharacteristicWeight k :=
  latticeCorrectionTerm_def_aux P k

/-- **The lattice correction term is the maximal normalized square of the orbit.** On a
negative-definite plumbing, `max_{k' ∈ [k]} (k'² + |V|) / 4 = (k² + |V|) / 4 - 2 m_k`, the maximum
being taken over the characteristic covectors `k'` spin^c equivalent to `k`. -/
theorem IsNegativeDefinite.isGreatest_latticeCorrectionTerm (h : P.IsNegativeDefinite)
    (k : P.characteristicVectors) :
    IsGreatest
      {q : ℚ | ∃ k', P.IsSpinCEquivalent k k' ∧ q = (P.covectorSquare k'.val + Fintype.card V) / 4}
      (P.latticeCorrectionTerm k) := by
  obtain ⟨⟨k₀, hk₀, hq₀⟩, hle⟩ := h.isGreatest_covectorSquare k
  constructor
  · refine ⟨k₀, hk₀, ?_⟩
    rw [latticeCorrectionTerm_def, ← hq₀]
    ring
  · rintro q ⟨k', hk', rfl⟩
    have := hle ⟨k', hk', rfl⟩
    rw [latticeCorrectionTerm_def]
    linarith

/-- **The lattice correction term depends only on the spin^c orbit.** On a negative-definite
plumbing, spin^c equivalent characteristic covectors have the same lattice correction term. -/
theorem IsNegativeDefinite.latticeCorrectionTerm_eq_of_isSpinCEquivalent
    (h : P.IsNegativeDefinite) {k k' : P.characteristicVectors} (hk : P.IsSpinCEquivalent k k') :
    P.latticeCorrectionTerm k' = P.latticeCorrectionTerm k := by
  have hset : {q : ℚ | ∃ k'', P.IsSpinCEquivalent k' k'' ∧
        q = (P.covectorSquare k''.val + Fintype.card V) / 4} =
      {q : ℚ | ∃ k'', P.IsSpinCEquivalent k k'' ∧
        q = (P.covectorSquare k''.val + Fintype.card V) / 4} := by
    ext q
    exact ⟨fun ⟨k'', h'', hq⟩ => ⟨k'', hk.trans P h'', hq⟩,
      fun ⟨k'', h'', hq⟩ => ⟨k'', hk.symm P |>.trans P h'', hq⟩⟩
  have h' := h.isGreatest_latticeCorrectionTerm k'
  rw [hset] at h'
  exact h'.unique (h.isGreatest_latticeCorrectionTerm k)

variable (P) in
/-- **Conjugation invariance.** The conjugate characteristic covector `-k` has the same lattice
correction term as `k`. -/
@[simp]
theorem latticeCorrectionTerm_conjugate (k : P.characteristicVectors) :
    P.latticeCorrectionTerm (P.conjugate k) = P.latticeCorrectionTerm k := by
  rw [latticeCorrectionTerm_def, latticeCorrectionTerm_def, conjugate_val, covectorSquare_neg,
    sInfCharacteristicWeight_conjugate]

end PlumbingGraph

end TauCeti
