/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Convex.Cone.Alternative
import Mathlib.Data.Rat.Cast.Order
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Integer
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import TauCeti.LinearAlgebra.Matrix.DotProduct

/-!
# Farkas certificates for finite systems of linear inequalities and equations

A finite system `A *ᵥ x ≤ b`, `E *ᵥ x = d` over a linearly ordered field `K` is described by a
matrix `A` of inequality rows and a matrix `E` of equality rows. A **Farkas certificate** is a pair
of multipliers: a *nonnegative* vector `y` for the inequality rows and an *unrestricted* vector `z`
for the equality rows. Every solution `x` satisfies
`(y ᵥ* A + z ᵥ* E) ⬝ᵥ x ≤ y ⬝ᵥ b + z ⬝ᵥ d` (`Matrix.vecMul_add_vecMul_dotProduct_le`), and Farkas'
lemma says that all consequences of the system arise in this way:

* an inequality `c ⬝ᵥ x ≤ δ` holds on a nonempty solution set exactly when `c = y ᵥ* A + z ᵥ* E` and
  `y ⬝ᵥ b + z ⬝ᵥ d ≤ δ` for some certificate
  (`Matrix.forall_dotProduct_le_iff_exists_vecMul_add_vecMul_eq`), with the homogeneous special
  case `Matrix.forall_dotProduct_nonpos_iff_exists_vecMul_add_vecMul_eq`;
* the system has no solution exactly when some certificate has `y ᵥ* A + z ᵥ* E = 0` and
  `y ⬝ᵥ b + z ⬝ᵥ d < 0` (`Matrix.not_exists_mulVec_le_and_mulVec_eq_iff`).
* an inequality `c ⬝ᵥ x ≤ δ` that no certificate implies is separated from the system by a
  vector `(u, s)` with `0 ≤ s`, even when the system has no solution
  (`Matrix.exists_dual_of_not_exists_vecMul_add_vecMul_eq_and_le`).

Equality multipliers must be allowed to take both signs: each equation contributes the two
inequalities `E j ⬝ᵥ x ≤ d j` and `-E j ⬝ᵥ x ≤ -d j`, and `z j` is the difference of their two
nonnegative multipliers.

The statements hold over every linearly ordered field, in particular over `ℚ`. Since
certificates are finite data, feasibility of a system with coefficients in `K` does not change
under an order-preserving ring homomorphism `K → L`
(`Matrix.exists_mulVec_le_and_mulVec_eq_map_iff`): a system with rational data that is solvable
over `ℝ` has a rational solution. Clearing the denominators of such a solution shows that a system
with integer data is solvable over `K` exactly when some dilation `A *ᵥ x ≤ N • b`, `E *ᵥ x = N • d`
with `0 < N` has an integer solution
(`Matrix.exists_mulVec_le_and_mulVec_eq_intCast_iff_exists_nsmul`).

Systems `A *ᵥ x ≤ b` without equality rows are the case `E := (0 : Matrix (Fin 0) ι K)`,
`d := 0`; the homogeneous form is stated for them directly
(`Matrix.forall_dotProduct_nonpos_iff_exists_vecMul_eq`).

## Implementation notes

Tucker's key lemma (`TauCeti.exists_nonneg_sum_smul_eq_zero_and_coeff_add_dual_pos_at`), applied
to the rows `(A i, b i)`, `±(E j, d j)`, `(0, 1)` of the homogenized system in `(ι → K) × K`
together with `-(c, δ)`, yields either a certificate or a solution of the homogenized system that
violates `c ⬝ᵥ x ≤ δ`. No topology or separation theorem is used.

## References

* J. Farkas, *Theorie der einfachen Ungleichungen*, J. Reine Angew. Math. **124** (1902), 1–27.
* A. Schrijver, *Theory of Linear and Integer Programming*, Wiley, 1986, §7.3, Corollaries 7.1e
  and 7.1h.
-/

public section

open scoped Matrix

namespace Matrix

variable {ι I J : Type*} [Fintype ι]

section OrderedSemiring

variable {R : Type*} [Semiring R] [PartialOrder R] [IsOrderedRing R]

/-- **Soundness of Farkas certificates.** If `y` is nonnegative, every solution of
`A *ᵥ x ≤ b`, `E *ᵥ x = d` satisfies the combined inequality
`(y ᵥ* A + z ᵥ* E) ⬝ᵥ x ≤ y ⬝ᵥ b + z ⬝ᵥ d`. -/
theorem vecMul_add_vecMul_dotProduct_le [Fintype I] [Fintype J] {A : Matrix I ι R} {b : I → R}
    {E : Matrix J ι R} {d : J → R} {x : ι → R} {y : I → R} (z : J → R) (hy : 0 ≤ y)
    (hA : A *ᵥ x ≤ b) (hE : E *ᵥ x = d) : (y ᵥ* A + z ᵥ* E) ⬝ᵥ x ≤ y ⬝ᵥ b + z ⬝ᵥ d := by
  rw [add_dotProduct, ← dotProduct_mulVec, ← dotProduct_mulVec, hE]
  exact add_le_add_left (dotProduct_le_dotProduct_of_nonneg_left hA hy) _

end OrderedSemiring

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Rescaling a solution of the homogenized system with positive last coordinate `t` gives a
solution of the original system. -/
private theorem mulVec_inv_smul {A : Matrix I ι K} {b : I → K} {E : Matrix J ι K} {d : J → K}
    {x : ι → K} {t : K} (ht : 0 < t) (hA : A *ᵥ x ≤ t • b) (hE : E *ᵥ x = t • d) :
    A *ᵥ (t⁻¹ • x) ≤ b ∧ E *ᵥ (t⁻¹ • x) = d := by
  refine ⟨?_, ?_⟩
  · rw [mulVec_smul, ← inv_smul_smul₀ ht.ne' b]
    exact smul_le_smul_of_nonneg_left hA (inv_nonneg.mpr ht.le)
  · rw [mulVec_smul, hE, inv_smul_smul₀ ht.ne']

/-- The homogenized Farkas alternative: either `c ⬝ᵥ x ≤ δ` has a certificate, or the homogenized
system `A *ᵥ x ≤ t • b`, `E *ᵥ x = t • d`, `0 ≤ t` has a solution with `t * δ < c ⬝ᵥ x`. -/
private theorem exists_certificate_or_exists [Fintype I] [Fintype J] (A : Matrix I ι K)
    (b : I → K) (E : Matrix J ι K) (d : J → K) (c : ι → K) (δ : K) :
    (∃ y, 0 ≤ y ∧ ∃ z, y ᵥ* A + z ᵥ* E = c ∧ y ⬝ᵥ b + z ⬝ᵥ d ≤ δ) ∨
      ∃ x t, 0 ≤ t ∧ A *ᵥ x ≤ t • b ∧ E *ᵥ x = t • d ∧ t * δ < c ⬝ᵥ x := by
  classical
  -- The rows `(A i, b i)`, `(E j, d j)`, `(-E j, -d j)` and `(0, 1)` generate the cone of
  -- inequalities implied by the system; the extra vector `-(c, δ)` sits at `none`.
  let a : Option (Option ((I ⊕ J) ⊕ J)) → (ι → K) × K := fun o =>
    o.elim (-(c, δ)) fun o' => o'.elim (0, 1) (Sum.elim (Sum.elim (fun i => (A i, b i))
      fun j => (E j, d j)) fun j => (-E j, -d j))
  obtain ⟨w, F, hw, hsum, hF, hpos⟩ :=
    TauCeti.exists_nonneg_sum_smul_eq_zero_and_coeff_add_dual_pos_at (K := K) a none
  rcases (hw none).lt_or_eq with hw₀ | hw₀
  · -- The relation involves `-(c, δ)`: dividing by its coefficient gives a certificate.
    set y : I → K := fun i => w (some (some (.inl (.inl i))))
    set z : J → K := fun j => w (some (some (.inl (.inr j)))) - w (some (some (.inr j)))
    have hfst := congrArg Prod.fst hsum
    have hsnd := congrArg Prod.snd hsum
    simp only [Fintype.sum_option, Fintype.sum_sum_type, Prod.fst_add, Prod.snd_add, Prod.fst_sum,
      Prod.snd_sum, Prod.smul_fst, Prod.smul_snd, Option.elim_none, Option.elim_some,
      Sum.elim_inl, Sum.elim_inr, Prod.fst_neg, Prod.snd_neg, Prod.fst_zero, Prod.snd_zero,
      a] at hfst hsnd
    have hc : y ᵥ* A + z ᵥ* E = w none • c := by
      rw [vecMul_eq_sum, vecMul_eq_sum]
      simp only [y, z, sub_smul, Finset.sum_sub_distrib, smul_neg, Finset.sum_neg_distrib,
        smul_zero, zero_add] at hfst ⊢
      linear_combination (norm := module) hfst
    have hδ : y ⬝ᵥ b + z ⬝ᵥ d + w (some none) = w none * δ := by
      simp only [dotProduct, y, z, sub_mul, Finset.sum_sub_distrib, smul_eq_mul, mul_neg,
        Finset.sum_neg_distrib, mul_one] at hsnd ⊢
      linear_combination hsnd
    refine .inl ⟨(w none)⁻¹ • y, fun i => mul_nonneg (inv_nonneg.mpr hw₀.le) (hw _), (w none)⁻¹ • z,
      ?_, ?_⟩
    · rw [smul_vecMul, smul_vecMul, ← smul_add, hc, inv_smul_smul₀ hw₀.ne']
    · rw [smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul, ← mul_add,
        inv_mul_le_iff₀ hw₀, ← hδ]
      exact le_add_of_nonneg_right (hw _)
  · -- The relation avoids `-(c, δ)`: the functional `F` separates `(c, δ)` from the cone.
    obtain ⟨x, t, hrep⟩ : ∃ (x : ι → K) (t : K), ∀ v r, F (v, r) = v ⬝ᵥ x + r * t :=
      ⟨_, _, F.apply_prod_eq_dotProduct_add_mul⟩
    have hF' : ∀ o, 0 ≤ F (a o) := hF
    simp only [a, Option.forall, Option.elim_none, Option.elim_some, Sum.forall, Sum.elim_inl,
      Sum.elim_inr, hrep, zero_dotProduct, one_mul, zero_add, neg_dotProduct] at hF'
    obtain ⟨-, ht, ⟨hA, hE⟩, hE'⟩ := hF'
    refine .inr ⟨-x, t, ht, fun i => ?_, funext fun j => ?_, ?_⟩
    · simp only [mulVec, dotProduct_neg, Pi.smul_apply, smul_eq_mul]
      linarith [hA i]
    · simp only [mulVec, dotProduct_neg, Pi.smul_apply, smul_eq_mul]
      linarith [hE j, hE' j]
    · simp only [← hw₀, Pi.zero_apply, zero_add, a, Option.elim_none, hrep, Prod.fst_neg,
        Prod.snd_neg, neg_dotProduct, neg_mul] at hpos
      rw [dotProduct_neg]
      linarith

/-- **Farkas certificate** for an inequality that is not a combination of a finite system: if
`(c, δ)` is not a combination `y ᵥ* A + z ᵥ* E = c`, `y ⬝ᵥ b + z ⬝ᵥ d ≤ δ` with `y` nonnegative,
then some `(u, s)` with `0 ≤ s` pairs nonnegatively with every row `(A i, b i)`, vanishes on every
row `(E j, d j)`, and pairs negatively with `(c, δ)`. No solvability of the system is assumed. -/
theorem exists_dual_of_not_exists_vecMul_add_vecMul_eq_and_le [Fintype I] [Fintype J]
    (A : Matrix I ι K) (b : I → K) (E : Matrix J ι K) (d : J → K) (c : ι → K) (δ : K)
    (h : ¬∃ y, 0 ≤ y ∧ ∃ z, y ᵥ* A + z ᵥ* E = c ∧ y ⬝ᵥ b + z ⬝ᵥ d ≤ δ) :
    ∃ (u : ι → K) (s : K), 0 ≤ s ∧ (∀ i, 0 ≤ A i ⬝ᵥ u + s * b i) ∧
      (∀ j, E j ⬝ᵥ u + s * d j = 0) ∧ c ⬝ᵥ u + s * δ < 0 := by
  obtain ⟨x, t, ht, hA, hE, hlt⟩ := (exists_certificate_or_exists A b E d c δ).resolve_left h
  refine ⟨-x, t, ht, fun i => ?_, fun j => ?_, ?_⟩
  · have hi := hA i
    simp only [mulVec, Pi.smul_apply, smul_eq_mul] at hi
    rw [dotProduct_neg]
    linarith
  · have hj := congrFun hE j
    simp only [mulVec, Pi.smul_apply, smul_eq_mul] at hj
    rw [dotProduct_neg]
    linarith
  · rw [dotProduct_neg]
    linarith

/-- **Farkas' lemma** for a nonempty solution set. On the solutions of `A *ᵥ x ≤ b`,
`E *ᵥ x = d`, if there are any, the inequality `c ⬝ᵥ x ≤ δ` holds exactly when it is implied by a
certificate: `c = y ᵥ* A + z ᵥ* E` and `y ⬝ᵥ b + z ⬝ᵥ d ≤ δ` with `y` nonnegative and `z`
arbitrary. -/
theorem forall_dotProduct_le_iff_exists_vecMul_add_vecMul_eq [Fintype I] [Fintype J]
    (A : Matrix I ι K) (b : I → K) (E : Matrix J ι K) (d : J → K) (c : ι → K) (δ : K)
    (hfeas : ∃ x, A *ᵥ x ≤ b ∧ E *ᵥ x = d) :
    (∀ x, A *ᵥ x ≤ b → E *ᵥ x = d → c ⬝ᵥ x ≤ δ) ↔
      ∃ y, 0 ≤ y ∧ ∃ z, y ᵥ* A + z ᵥ* E = c ∧ y ⬝ᵥ b + z ⬝ᵥ d ≤ δ := by
  refine ⟨fun hvalid => (exists_certificate_or_exists A b E d c δ).resolve_right ?_, ?_⟩
  · rintro ⟨x, t, ht, hA, hE, hlt⟩
    rcases ht.lt_or_eq with ht | rfl
    · -- `t⁻¹ • x` is a solution violating the inequality.
      obtain ⟨hA', hE'⟩ := mulVec_inv_smul ht hA hE
      have h := hvalid _ hA' hE'
      rw [dotProduct_smul, smul_eq_mul, inv_mul_le_iff₀ ht] at h
      exact h.not_gt (by linarith)
    · -- `x` is a recession direction along which `c ⬝ᵥ x` increases without bound.
      obtain ⟨x₀, hA₀, hE₀⟩ := hfeas
      rw [zero_smul] at hA hE
      rw [zero_mul] at hlt
      set μ : K := (|δ - c ⬝ᵥ x₀| + 1) / (c ⬝ᵥ x)
      have hμ : 0 ≤ μ := div_nonneg (by positivity) hlt.le
      have h := hvalid (x₀ + μ • x)
        (by rw [mulVec_add, mulVec_smul, ← add_zero b]
            exact add_le_add hA₀ (smul_nonpos_of_nonneg_of_nonpos hμ hA))
        (by rw [mulVec_add, mulVec_smul, hE, hE₀, smul_zero, add_zero])
      rw [dotProduct_add, dotProduct_smul, smul_eq_mul, div_mul_cancel₀ _ hlt.ne'] at h
      linarith [le_abs_self (δ - c ⬝ᵥ x₀)]
  · rintro ⟨y, hy, z, rfl, hle⟩ x hA hE
    exact (vecMul_add_vecMul_dotProduct_le z hy hA hE).trans hle

/-- **Farkas' lemma**, homogeneous form. The inequality `c ⬝ᵥ x ≤ 0` holds on the polyhedral cone
`A *ᵥ x ≤ 0`, `E *ᵥ x = 0` exactly when `c = y ᵥ* A + z ᵥ* E` with `y` nonnegative and `z`
arbitrary. -/
theorem forall_dotProduct_nonpos_iff_exists_vecMul_add_vecMul_eq [Fintype I] [Fintype J]
    (A : Matrix I ι K) (E : Matrix J ι K) (c : ι → K) :
    (∀ x, A *ᵥ x ≤ 0 → E *ᵥ x = 0 → c ⬝ᵥ x ≤ 0) ↔ ∃ y, 0 ≤ y ∧ ∃ z, y ᵥ* A + z ᵥ* E = c := by
  simpa using forall_dotProduct_le_iff_exists_vecMul_add_vecMul_eq A 0 E 0 c 0
    ⟨0, by simp, by simp⟩

/-- **Farkas' lemma**, infeasibility form. The system `A *ᵥ x ≤ b`, `E *ᵥ x = d` has no solution
exactly when some certificate, with `y` nonnegative and `z` arbitrary, combines it into the
contradiction `0 ≤ y ⬝ᵥ b + z ⬝ᵥ d < 0`. -/
theorem not_exists_mulVec_le_and_mulVec_eq_iff [Fintype I] [Fintype J] (A : Matrix I ι K)
    (b : I → K) (E : Matrix J ι K) (d : J → K) :
    (¬∃ x, A *ᵥ x ≤ b ∧ E *ᵥ x = d) ↔
      ∃ y, 0 ≤ y ∧ ∃ z, y ᵥ* A + z ᵥ* E = 0 ∧ y ⬝ᵥ b + z ⬝ᵥ d < 0 := by
  refine ⟨fun hne => ?_, ?_⟩
  · rcases exists_certificate_or_exists A b E d 0 (-1) with
      ⟨y, hy, z, h0, hle⟩ | ⟨x, t, -, hA, hE, hlt⟩
    · exact ⟨y, hy, z, h0, hle.trans_lt (by norm_num)⟩
    · rw [zero_dotProduct, mul_neg_one, neg_neg_iff_pos] at hlt
      exact (hne ⟨_, mulVec_inv_smul hlt hA hE⟩).elim
  · rintro ⟨y, hy, z, h0, hlt⟩ ⟨x, hA, hE⟩
    have h := vecMul_add_vecMul_dotProduct_le z hy hA hE
    rw [h0, zero_dotProduct] at h
    exact (h.trans_lt hlt).false

/-- Feasibility of a finite system of linear inequalities and equations does not change under an
order-preserving ring homomorphism out of a linearly ordered field: a Farkas certificate of
infeasibility over `K` maps to one over `L`. For instance, a system with rational coefficients
that is solvable over `ℝ` has a rational solution. -/
theorem exists_mulVec_le_and_mulVec_eq_map_iff [Finite I] [Finite J] {L : Type*} [Semiring L]
    [PartialOrder L] [IsOrderedRing L] [Nontrivial L] (f : K →+* L) (hf : Monotone f)
    (A : Matrix I ι K) (b : I → K) (E : Matrix J ι K) (d : J → K) :
    (∃ x, A.map f *ᵥ x ≤ f ∘ b ∧ E.map f *ᵥ x = f ∘ d) ↔ ∃ x, A *ᵥ x ≤ b ∧ E *ᵥ x = d := by
  refine ⟨fun ⟨x, hA, hE⟩ => ?_, fun ⟨x, hA, hE⟩ => ⟨f ∘ x, fun i => ?_, funext fun j => ?_⟩⟩
  · cases nonempty_fintype I
    cases nonempty_fintype J
    by_contra hne
    obtain ⟨y, hy, z, h0, hlt⟩ := (not_exists_mulVec_le_and_mulVec_eq_iff A b E d).mp hne
    have hmap : (f ∘ y) ᵥ* A.map f + (f ∘ z) ᵥ* E.map f = 0 := by
      ext k
      simpa [← RingHom.map_vecMul] using congrArg (fun v => f (v k)) h0
    have h := vecMul_add_vecMul_dotProduct_le (y := f ∘ y) (f ∘ z)
      (fun i => by simpa using hf (hy i)) hA hE
    rw [hmap, zero_dotProduct, ← RingHom.map_dotProduct, ← RingHom.map_dotProduct, ← map_add] at h
    exact h.not_gt (by simpa using (hf.strictMono_of_injective f.injective) hlt)
  · simpa [← RingHom.map_mulVec] using hf (hA i)
  · simpa [← RingHom.map_mulVec] using congrArg f (congrFun hE j)

/-- **Clearing denominators.** A finite system `A *ᵥ x ≤ b`, `E *ᵥ x = d` with integer coefficients
is solvable over a linearly ordered field `K`, for instance `ℝ`, exactly when for some positive `N`
the dilated system `A *ᵥ x ≤ N • b`, `E *ᵥ x = N • d` has an integer solution. -/
theorem exists_mulVec_le_and_mulVec_eq_intCast_iff_exists_nsmul [Finite I] [Finite J]
    (A : Matrix I ι ℤ) (b : I → ℤ) (E : Matrix J ι ℤ) (d : J → ℤ) :
    (∃ x : ι → K, A.map (Int.cast : ℤ → K) *ᵥ x ≤ Int.cast ∘ b ∧
        E.map (Int.cast : ℤ → K) *ᵥ x = Int.cast ∘ d) ↔
      ∃ N : ℕ, 0 < N ∧ ∃ x : ι → ℤ, A *ᵥ x ≤ N • b ∧ E *ᵥ x = N • d := by
  constructor
  · intro hK
    obtain ⟨q, hqA, hqE⟩ := (exists_mulVec_le_and_mulVec_eq_map_iff (Rat.castHom K) Rat.cast_mono
      (A.map Int.cast) (Int.cast ∘ b) (E.map Int.cast) (Int.cast ∘ d)).mp
      (by simpa [Matrix.map_map, Function.comp_def] using hK)
    -- Clear the denominators of the rational solution `q` by a positive integer `D`.
    obtain ⟨⟨D, hD⟩, hDq⟩ := IsLocalization.exist_integer_multiples_of_finite (Submonoid.pos ℤ) q
    choose g hg using hDq
    rw [Submonoid.mem_pos] at hD
    have hD' : (0 : ℚ) < D := by exact_mod_cast hD
    have hg' : (Int.cast ∘ g : ι → ℚ) = (D : ℚ) • q := funext fun k => by simpa using hg k
    refine ⟨D.toNat, by omega, g, fun i => ?_, funext fun j => ?_⟩
    · have h : ((A *ᵥ g) i : ℚ) = ((D : ℚ) • (A.map Int.cast *ᵥ q)) i := by
        rw [← mulVec_smul, ← hg']
        exact (Int.castRingHom ℚ).map_mulVec A g i
      rw [← Int.cast_le (R := ℚ), h]
      simpa [max_eq_left hD'.le] using mul_le_mul_of_nonneg_left (hqA i) hD'.le
    · have h : ((E *ᵥ g) j : ℚ) = ((D : ℚ) • (E.map Int.cast *ᵥ q)) j := by
        rw [← mulVec_smul, ← hg']
        exact (Int.castRingHom ℚ).map_mulVec E g j
      apply Int.cast_injective (α := ℚ)
      have hqj : (E.map Int.cast *ᵥ q) j = d j := by simpa using congrFun hqE j
      simp [h, hqj, max_eq_left hD'.le]
  · rintro ⟨N, hN, x, hA, hE⟩
    have hN' : (0 : K) < N := by exact_mod_cast hN
    refine ⟨_, mulVec_inv_smul hN' (x := Int.cast ∘ x) (fun i => ?_) (funext fun j => ?_)⟩
    · have h : ((A *ᵥ x) i : K) = (A.map Int.cast *ᵥ (Int.cast ∘ x)) i :=
        (Int.castRingHom K).map_mulVec A x i
      rw [← h]
      simpa using (Int.cast_le (R := K)).mpr (hA i)
    · have h : ((E *ᵥ x) j : K) = (E.map Int.cast *ᵥ (Int.cast ∘ x)) j :=
        (Int.castRingHom K).map_mulVec E x j
      rw [← h]
      simpa using congrArg (Int.cast : ℤ → K) (congrFun hE j)

/-! ### Systems of linear inequalities

The special case of the results above in which there are no equality rows. -/

/-- **Farkas' lemma**, homogeneous form without equality rows. The inequality `c ⬝ᵥ x ≤ 0` holds on
the polyhedral cone `A *ᵥ x ≤ 0` exactly when `c = y ᵥ* A` for some nonnegative `y`. -/
theorem forall_dotProduct_nonpos_iff_exists_vecMul_eq [Fintype I] (A : Matrix I ι K)
    (c : ι → K) : (∀ x, A *ᵥ x ≤ 0 → c ⬝ᵥ x ≤ 0) ↔ ∃ y, 0 ≤ y ∧ y ᵥ* A = c := by
  simpa using forall_dotProduct_nonpos_iff_exists_vecMul_add_vecMul_eq A
    (0 : Matrix (Fin 0) ι K) c

end Matrix
