/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TensorCoalgebra.Brace
public import TauCeti.LinearAlgebra.TensorCoalgebra.CoalgHom

/-!
# Tensor words containing a distinguished element

The degenerate words associated to an element `e` are the span of the nonempty pure tensor
words with at least one letter equal to `e`. For a unit, these are the words discarded by
normalization of the bar construction. A coalgebra morphism preserves this submodule if its
linear component preserves the distinguished element and its higher Taylor components vanish
on words containing it.

A Taylor map vanishing on higher degenerate words agrees there with its linear component
composed with the letter projection. These two facts let one prove closure of normalized
Taylor maps under coalgebra composition without choosing a formula indexed by partitions.

For a homogeneous `e`, the graded Taylor expansion of a map vanishing on degenerate words
preserves them: a collapsed block containing `e` contributes nothing, and any other collapse
keeps the letter `e`, up to the sign of the Koszul twist.  Hence the brace and the Gerstenhaber
bracket of two such maps vanish on degenerate words again; these are the normalized Hochschild
cochains.  Degenerate words are also spanned by the pure words of homogeneous letters with a
letter equal to `e`, so vanishing on them may be tested on homogeneous inputs
(`degenerateWords_le_iff_of_mem_piece`).

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.4 and 3.6.
* E. Getzler and J. D. S. Jones, *A-infinity algebras and the cyclic bar complex*, Sections 1--2.
-/

public section

open scoped TensorProduct

namespace TauCeti.ReducedTensorWords

universe uR uM uN

variable (R : Type uR) (M : Type uM) [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- The span of nonempty pure tensor words containing the distinguished element `e`.
The one-letter word `e` is included. -/
noncomputable def degenerateWords (e : M) : Submodule R (ReducedTensorWords R M) :=
  Submodule.span R {z | ∃ (n : {n : ℕ // 0 < n}) (x : Fin n.1 → M),
    (∃ i, x i = e) ∧ z = of R M n (PiTensorProduct.tprod R x)}

variable {R M}

/-- A submodule contains all degenerate words exactly when it contains each pure tensor word
with a distinguished letter. This is the universal property of their span. -/
@[simp]
theorem degenerateWords_le_iff {e : M} {S : Submodule R (ReducedTensorWords R M)} :
    degenerateWords R M e ≤ S ↔ ∀ (n : {n : ℕ // 0 < n}) (x : Fin n.1 → M),
      (∃ i, x i = e) → of R M n (PiTensorProduct.tprod R x) ∈ S := by
  rw [degenerateWords, Submodule.span_le]
  constructor
  · intro h n x hx
    exact h ⟨n, x, hx, rfl⟩
  · intro h z hz
    obtain ⟨n, x, hx, rfl⟩ := hz
    exact h n x hx

/-- A pure tensor word containing `e` is degenerate. -/
theorem of_tprod_mem_degenerateWords {e : M} (n : {n : ℕ // 0 < n})
    (x : Fin n.1 → M) (hx : ∃ i, x i = e) :
    of R M n (PiTensorProduct.tprod R x) ∈ degenerateWords R M e :=
  Submodule.subset_span ⟨n, x, hx, rfl⟩

/-- A block containing `e` is degenerate. -/
theorem subword_mem_degenerateWords {e : M} {n : ℕ} (x : Fin n → M) {a b : ℕ}
    (hab : a + b ≤ n) (hx : ∃ i : Fin n, a ≤ i.1 ∧ i.1 < a + b ∧ x i = e) :
    subword R x a b ∈ degenerateWords R M e := by
  obtain ⟨i, hai, hib, hi⟩ := hx
  have hb : 0 < b := by omega
  rw [subword_eq_of_tprod R x hb hab]
  apply of_tprod_mem_degenerateWords
  have hj : i.1 - a < b := by omega
  refine ⟨⟨i.1 - a, hj⟩, ?_⟩
  convert hi using 1
  congr 1
  apply Fin.ext
  simp only [Nat.add_sub_of_le hai]

/-- The one-letter word `e` is degenerate. -/
theorem ofLetter_mem_degenerateWords (e : M) :
    ofLetter R M e ∈ degenerateWords R M e := by
  rw [← subword_one R M (fun _ : Fin 1 ↦ e) Nat.one_pos]
  exact subword_mem_degenerateWords _ (by omega) ⟨0, by omega, by omega, rfl⟩

/-- Prepending an arbitrary letter preserves degeneracy. -/
theorem prepend_mem_degenerateWords {e : M} (a : M) {z : ReducedTensorWords R M}
    (hz : z ∈ degenerateWords R M e) :
    prepend R M a z ∈ degenerateWords R M e := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨n, x, ⟨i, hi⟩, rfl⟩ := hz
    rw [prepend_of_tprod]
    exact of_tprod_mem_degenerateWords _ _ ⟨i.succ, by simpa using hi⟩
  | zero => simp
  | add x y _ _ hx hy => simpa using (degenerateWords R M e).add_mem hx hy
  | smul c x _ hx => simpa using (degenerateWords R M e).smul_mem c hx

/-- Prepending the distinguished element makes every reduced tensor word degenerate. -/
theorem prepend_distinguished_mem_degenerateWords (e : M) (z : ReducedTensorWords R M) :
    prepend R M e z ∈ degenerateWords R M e := by
  have hle : (⊤ : Submodule R (ReducedTensorWords R M)) ≤
      (degenerateWords R M e).comap (prepend R M e) := by
    rw [← iSup_range_of R M, iSup_le_iff]
    intro n
    rw [LinearMap.range_le_iff_comap]
    apply top_unique
    intro t ht
    clear ht
    induction t using PiTensorProduct.induction_on with
    | smul_tprod c x =>
      simp only [map_smul, Submodule.mem_comap]
      apply Submodule.smul_mem
      rw [prepend_of_tprod]
      exact of_tprod_mem_degenerateWords _ _ ⟨0, rfl⟩
    | add t u ht hu => simpa using Submodule.add_mem _ ht hu
  exact hle (Submodule.mem_top)

variable {N : Type uN} [AddCommMonoid N] [Module R N]

/-- On degenerate words, a Taylor map that vanishes in higher arities is its linear component
composed with the letter projection. -/
theorem apply_eq_comp_letter_of_mem_degenerateWords
    (f : ReducedTensorWords R M →ₗ[R] N) {e : M}
    (hf : ∀ (n : {n : ℕ // 0 < n}), n.1 ≠ 1 → ∀ x : Fin n.1 → M,
      (∃ i, x i = e) → f (of R M n (PiTensorProduct.tprod R x)) = 0)
    {z : ReducedTensorWords R M} (hz : z ∈ degenerateWords R M e) :
    f z = f (ofLetter R M (letter R M z)) := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨n, x, hx, rfl⟩ := hz
    by_cases hn : n.1 = 1
    · obtain ⟨k, hk⟩ := n
      simp only at hn
      subst k
      rw [of_tprod_eq_subword R hk, subword_one R M x (by omega), letter_ofLetter]
    · rw [hf n hn x hx, of_tprod_eq_subword R n.2,
        letter_subword_of_ne_one R M x 0 hn, map_zero, map_zero]
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul c x _ hx => simp only [map_smul, hx]

/-- The Taylor expansion of a block containing the distinguished element is degenerate. -/
theorem coalgHom_subword_mem_degenerateWords (f : ReducedTensorWords R M →ₗ[R] N)
    {e : M} {e' : N} (he : f (ofLetter R M e) = e')
    (hf : ∀ (n : {n : ℕ // 0 < n}), n.1 ≠ 1 → ∀ x : Fin n.1 → M,
      (∃ i, x i = e) → f (of R M n (PiTensorProduct.tprod R x)) = 0)
    {n : ℕ} (x : Fin n → M) {a b : ℕ} (hab : a + b ≤ n)
    (hx : ∃ i : Fin n, a ≤ i.1 ∧ i.1 < a + b ∧ x i = e) :
    coalgHom R f (subword R x a b) ∈ degenerateWords R N e' := by
  suffices hblock : ∀ b (a n : ℕ) (x : Fin n → M), a + b ≤ n →
      (∃ i : Fin n, a ≤ i.1 ∧ i.1 < a + b ∧ x i = e) →
      coalgHom R f (subword R x a b) ∈ degenerateWords R N e' from hblock b a n x hab hx
  intro b
  induction b using Nat.strong_induction_on with
  | h b ih =>
    intro a n x hab hx
    obtain ⟨i, hai, hib, hi⟩ := hx
    have hb : 0 < b := by omega
    have hvanish : ∀ c, 1 < c → a + c ≤ n → i.1 < a + c →
        f (subword R x a c) = 0 := by
      intro c hc hac hic
      rw [apply_eq_comp_letter_of_mem_degenerateWords f hf
        (subword_mem_degenerateWords x hac ⟨i, hai, hic, hi⟩),
        letter_subword_of_ne_one R M x a (by omega), map_zero, map_zero]
    -- The recursion separates the single-letter output from the proper cuts.
    rw [coalgHom_subword]
    apply Submodule.add_mem
    · by_cases hb1 : b = 1
      · have hie : i.1 = a := by omega
        have hsingle : subword R x a b = ofLetter R M e := by
          rw [hb1, subword_one R M x (by omega)]
          congr 1
          convert hi using 1
          congr 1
          exact Fin.ext hie.symm
        rw [hsingle, he]
        exact ofLetter_mem_degenerateWords e'
      · rw [hvanish b (by omega) hab hib, map_zero]
        exact Submodule.zero_mem _
    · apply Submodule.sum_mem
      intro d hd
      have hdlt : d < b := Finset.mem_range.mp hd
      -- A distinguished letter in the first block survives only in a singleton block.
      by_cases hid : i.1 < a + d
      · by_cases hd1 : d = 1
        · have hie : i.1 = a := by omega
          rw [hd1, subword_one R M x (by omega)]
          have hea : x ⟨a, by omega⟩ = e := by
            convert hi using 1
            congr 1
            exact Fin.ext hie.symm
          rw [hea, he]
          exact prepend_distinguished_mem_degenerateWords _ _
        · rw [hvanish d (by omega) (by omega) hid, LinearMap.map_zero]
          exact Submodule.zero_mem _
      · by_cases hd0 : d = 0
        · simp only [hd0, subword_length_zero, map_zero, LinearMap.zero_apply,
            Submodule.zero_mem]
        -- Otherwise the distinguished letter lies in the shorter tail.
        · apply prepend_mem_degenerateWords
          apply ih (b - d) (by omega) (a + d) n x (by omega)
          exact ⟨i, by omega, by omega, hi⟩

/-- A coalgebra Taylor expansion preserves degenerate words when its linear component carries
`e` to `e'` and every higher component vanishes on words containing `e`. -/
theorem coalgHom_mem_degenerateWords (f : ReducedTensorWords R M →ₗ[R] N)
    {e : M} {e' : N} (he : f (ofLetter R M e) = e')
    (hf : ∀ (n : {n : ℕ // 0 < n}), n.1 ≠ 1 → ∀ x : Fin n.1 → M,
      (∃ i, x i = e) → f (of R M n (PiTensorProduct.tprod R x)) = 0)
    {z : ReducedTensorWords R M} (hz : z ∈ degenerateWords R M e) :
    coalgHom R f z ∈ degenerateWords R N e' := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨n, x, hx, rfl⟩ := hz
    rw [of_tprod_eq_subword R n.2]
    apply coalgHom_subword_mem_degenerateWords f he hf x (by omega)
    obtain ⟨i, hi⟩ := hx
    exact ⟨i, by omega, by simp, hi⟩
  | zero => simp
  | add x y _ _ hx hy => simpa using Submodule.add_mem _ hx hy
  | smul c x _ hx => simpa using Submodule.smul_mem _ c hx

/-! ### Graded Taylor expansions and homogeneous spanning words -/

section Graded

variable {R : Type uR} {M : Type uM} [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- A pure tensor word one of whose letters is a scalar multiple of `e` is degenerate. -/
theorem of_tprod_mem_degenerateWords_of_eq_smul {e : M} (n : {n : ℕ // 0 < n})
    (x : Fin n.1 → M) {i : Fin n.1} {c : R} (hi : x i = c • e) :
    of R M n (PiTensorProduct.tprod R x) ∈ degenerateWords R M e := by
  have hx : x = Function.update x i (c • e) := by rw [← hi, Function.update_eq_self]
  rw [hx, (PiTensorProduct.tprod R).map_update_smul, map_smul]
  exact Submodule.smul_mem _ _ (of_tprod_mem_degenerateWords _ _ ⟨i, by simp⟩)

/-- Vanishing on degenerate words may be tested on pure words of homogeneous letters, one of which
is the homogeneous element `e` with its degree. -/
theorem degenerateWords_le_iff_of_mem_piece (G : InternalGrading R M) {e : M} {E : ℤ}
    (he : e ∈ G.piece E) {S : Submodule R (ReducedTensorWords R M)} :
    degenerateWords R M e ≤ S ↔ ∀ (n : {n : ℕ // 0 < n}) (x : Fin n.1 → M) (𝒟 : Fin n.1 → ℤ)
      (i : Fin n.1), (∀ j, x j ∈ G.piece (𝒟 j)) → x i = e → 𝒟 i = E →
        of R M n (PiTensorProduct.tprod R x) ∈ S := by
  classical
  refine ⟨fun h n x 𝒟 i _ hi _ ↦ h (of_tprod_mem_degenerateWords n x ⟨i, hi⟩), fun h ↦ ?_⟩
  rw [degenerateWords_le_iff]
  rintro n x ⟨i, hi⟩
  -- Expand every letter except the `i`-th one into its homogeneous components.
  let support : Fin n.1 → Finset ℤ := fun j ↦
    if j = i then {E} else (DirectSum.decompose G.piece (x j)).support
  let component : Fin n.1 → ℤ → M := fun j p ↦
    if j = i then e else DirectSum.decompose G.piece (x j) p
  have hx (j : Fin n.1) : ∑ p ∈ support j, component j p = x j := by
    by_cases hj : j = i
    · subst hj
      simp [support, component, hi]
    · simpa [support, component, hj] using DirectSum.sum_support_decompose G.piece (x j)
  have htuple : PiTensorProduct.tprod R x =
      ∑ 𝒟 ∈ Fintype.piFinset support, PiTensorProduct.tprod R fun j ↦ component j (𝒟 j) := by
    rw [← (PiTensorProduct.tprod R).map_sum_finset]
    exact congrArg _ (funext fun j ↦ (hx j).symm)
  rw [htuple, map_sum]
  refine Submodule.sum_mem _ fun 𝒟 h𝒟 ↦ ?_
  have h𝒟i : 𝒟 i = E := by
    simpa [support] using Fintype.mem_piFinset.1 h𝒟 i
  refine h n _ 𝒟 i (fun j ↦ ?_) (by simp [component]) h𝒟i
  by_cases hj : j = i
  · subst hj
    simpa [component, h𝒟i] using he
  · simp [component, hj]

section Coderivation

variable {R : Type uR} {M : Type uM} [CommRing R] [AddCommMonoid M] [Module R M]

/-- The graded Taylor expansion of a map vanishing on the degenerate words of a homogeneous `e`
preserves those words: a collapsed block containing `e` is killed, and every other collapse keeps
the letter `e`, possibly twisted by a sign. -/
theorem gradedCoderiv_mem_degenerateWords (G : InternalGrading R M)
    {F : ReducedTensorWords R M →ₗ[R] M} (q : ℤ) {e : M} {E : ℤ} (he : e ∈ G.piece E)
    (hF : degenerateWords R M e ≤ LinearMap.ker F) {z : ReducedTensorWords R M}
    (hz : z ∈ degenerateWords R M e) : gradedCoderiv G F q z ∈ degenerateWords R M e := by
  suffices hle : degenerateWords R M e ≤ (degenerateWords R M e).comap (gradedCoderiv G F q) from
    hle hz
  rw [degenerateWords_le_iff]
  rintro ⟨n, hn⟩ x ⟨i, hi⟩
  have hin : i.1 < n := i.isLt
  rw [Submodule.mem_comap, gradedCoderiv_of_tprod]
  refine Submodule.sum_mem _ fun p _ ↦ Submodule.sum_mem _ fun d _ ↦ ?_
  by_cases hfit : 0 < d ∧ p + d ≤ n
  swap
  · rw [splice_eq_zero_of_not_fits R _ _ hfit]
    exact Submodule.zero_mem _
  by_cases hblock : p ≤ i.1 ∧ i.1 < p + d
  · -- The collapsed block contains `e`, so `F` kills it.
    rw [hF (subword_mem_degenerateWords x hfit.2 ⟨i, hblock.1, hblock.2, hi⟩), splice_zero]
    exact Submodule.zero_mem _
  -- Otherwise the letter `e` survives, twisted by a sign when it precedes the collapsed block.
  obtain ⟨y, ⟨k, hk⟩, hy⟩ := exists_splice_eq_of_tprod R _ hfit.1 hfit.2
    (F (subword R x p d)) hblock
  rw [hy]
  refine of_tprod_mem_degenerateWords_of_eq_smul _ _ (i := k)
    (c := if i.1 < p then (((q * E).negOnePow : ℤ) : R) else 1) ?_
  rw [hk, InternalGrading.twistedTuple_apply, hi]
  split_ifs with h₁ h₂ h₂
  · exact G.koszulTwist_apply_of_mem he q
  · omega
  · omega
  · rw [one_smul]

end Coderivation

section Brace

variable {R : Type uR} {M : Type uM} [CommRing R] [AddCommGroup M] [Module R M]

/-- The brace of two maps vanishing on the degenerate words of a homogeneous `e` vanishes on
them. -/
theorem degenerateWords_le_ker_brace (G : InternalGrading R M)
    {F g : ReducedTensorWords R M →ₗ[R] M} (q : ℤ) {e : M} {E : ℤ} (he : e ∈ G.piece E)
    (hF : degenerateWords R M e ≤ LinearMap.ker F)
    (hg : degenerateWords R M e ≤ LinearMap.ker g) :
    degenerateWords R M e ≤ LinearMap.ker (brace G F g q) := fun _ hz ↦ by
  rw [LinearMap.mem_ker, brace_def, LinearMap.comp_apply]
  exact hF (gradedCoderiv_mem_degenerateWords G q he hg hz)

/-- The Gerstenhaber bracket of two maps vanishing on the degenerate words of a homogeneous `e`
vanishes on them. -/
theorem degenerateWords_le_ker_gerstenhaberBracket (G : InternalGrading R M)
    {F g : ReducedTensorWords R M →ₗ[R] M} (p q : ℤ) {e : M} {E : ℤ} (he : e ∈ G.piece E)
    (hF : degenerateWords R M e ≤ LinearMap.ker F)
    (hg : degenerateWords R M e ≤ LinearMap.ker g) :
    degenerateWords R M e ≤ LinearMap.ker (gerstenhaberBracket G p q F g) := fun z hz ↦ by
  rw [LinearMap.mem_ker, gerstenhaberBracket_def, LinearMap.sub_apply, LinearMap.smul_apply,
    degenerateWords_le_ker_brace G q he hF hg hz, degenerateWords_le_ker_brace G p he hg hF hz,
    smul_zero, sub_zero]

end Brace

end Graded

end TauCeti.ReducedTensorWords
