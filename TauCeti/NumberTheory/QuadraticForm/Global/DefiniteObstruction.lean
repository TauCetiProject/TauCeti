/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.QuadraticForm.Global.Predicates
public import TauCeti.NumberTheory.QuadraticForm.Global.Signature
import TauCeti.LinearAlgebra.QuadraticForm.Diagonal.Basic
import TauCeti.NumberTheory.NumberField.Units.Signature.Integer
import TauCeti.NumberTheory.QuadraticForm.Global.AnisotropicPlaces

/-!
# Isotropy at every completion but one real place

The Hasse–Minkowski theorem asks for isotropy at *every* finite and real completion, and no single
real place can be omitted. Let `K` be a number field with a real place `w₀`, and let `a ∈ Kˣ` be
positive at `w₀` and negative at every other real place; such an `a` exists because every pattern
of signs at the real places is realized by an element of `Kˣ`. For every `n ≥ 4` the diagonal form

```text
Q = ⟨a, 1, …, 1⟩        (rank n + 1 ≥ 5)
```

is regular and

* isotropic at every finite place, because a regular form of rank at least five over a
  nonarchimedean local field is isotropic;
* isotropic at every real place `w ≠ w₀`, where it is indefinite;
* anisotropic at `w₀`, where it is positive definite, and therefore anisotropic over `K`.

So isotropy at all completions but one does not imply global isotropy. If `K` has a second real
place `w₁ ≠ w₀`, the form is indefinite at `w₁`, so indefiniteness at one real embedding does not
imply global isotropy either. Over `ℚ`, with its single real place, one may take `a = 1`, giving
the sum of `n + 1` squares.

In rank at least five every form is isotropic at every finite place, so in these ranks only a
real place can be the omitted one.

## Main results

* `TauCeti.NumberField.QuadraticForm.exists_anisotropic_and_not_anisotropic_away_from_realPlace`:
  for every real place `w₀` and every rank at least five, a regular form isotropic at every finite
  place and at every real place other than `w₀`, but anisotropic at `w₀` and over `K`.

## References

* J.-P. Serre, *A Course in Arithmetic*, Springer (1973), Chapter IV, §2.2, Theorem 6 (iv) for
  isotropy in dimension at least five over a local field, and §3 for the Hasse–Minkowski theorem.
* O. T. O'Meara, *Introduction to Quadratic Forms*, Springer (1963), §66.
-/

public section
noncomputable section

open IsDedekindDomain NumberField NumberField.InfinitePlace QuadraticMap

namespace TauCeti.NumberField.QuadraticForm

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

/-- **Isotropy at every completion but one does not imply isotropy.** For every real place `w₀`
of a number field `K` and every `n ≥ 4` there is a regular quadratic form of rank `n + 1` which is
isotropic at every finite place and at every real place other than `w₀`, but is anisotropic at
`w₀` and over `K`. It is `⟨a, 1, …, 1⟩` for an `a ∈ Kˣ` positive at `w₀` and negative at every
other real place. -/
theorem exists_anisotropic_and_not_anisotropic_away_from_realPlace
    (w₀ : {w : InfinitePlace K // w.IsReal}) (hn : 4 ≤ n) :
    ∃ Q : _root_.QuadraticForm K (Fin (n + 1) → K), Q.Nondegenerate ∧ Q.Anisotropic ∧
      (Q.atRealPlace w₀).Anisotropic ∧
      (∀ v : HeightOneSpectrum (𝓞 K), ¬ (Q.atFinitePlace v).Anisotropic) ∧
      ∀ w : {w : InfinitePlace K // w.IsReal}, w ≠ w₀ → ¬ (Q.atRealPlace w).Anisotropic := by
  classical
  -- A field unit with sign `+1` at `w₀` and `-1` at every other real place.
  obtain ⟨a, ha⟩ := TauCeti.GlobalNumberFields.signHom_surjective (K := K)
    fun w => if w = w₀ then 1 else -1
  have hpos : 0 < embedding_of_isReal w₀.2 (a : K) :=
    (TauCeti.GlobalNumberFields.signHom_apply_eq_one_iff a w₀).mp (by rw [ha]; simp)
  have hneg (w : {w : InfinitePlace K // w.IsReal}) (hw : w ≠ w₀) :
      embedding_of_isReal w.2 (a : K) < 0 :=
    (TauCeti.GlobalNumberFields.signHom_apply_eq_neg_one_iff a w).mp (by rw [ha]; simp [hw])
  set c : Fin (n + 1) → K := Fin.cons (a : K) 1
  have hc (i : Fin (n + 1)) : c i ≠ 0 := by
    cases i using Fin.cases <;> simp [c]
  set Q : _root_.QuadraticForm K (Fin (n + 1) → K) := weightedSumSquares K c
  have hQ : Q.Nondegenerate :=
    nondegenerate_weightedSumSquares fun i => isRegular_iff_ne_zero.mpr (hc i)
  -- At `w₀` every coefficient is positive, so `Q` is positive definite there.
  have hQ₀ : (Q.atRealPlace w₀).Anisotropic := by
    refine (_root_.QuadraticForm.anisotropic_atRealPlace_weightedSumSquares_iff c w₀).mpr
      (Or.inl fun i => ?_)
    cases i using Fin.cases <;> simp [c, hpos]
  -- An isotropic vector over `K` would stay isotropic at `w₀`.
  have hQK : Q.Anisotropic := by
    by_contra h
    exact ((_root_.QuadraticForm.isLocallyIsotropic_iff Q).mp
      (_root_.QuadraticForm.isLocallyIsotropic_of_not_anisotropic Q h)).2 w₀ hQ₀
  refine ⟨Q, hQ, hQK, hQ₀,
    _root_.QuadraticForm.not_anisotropic_atFinitePlace_of_five_le_finrank Q
      (by rw [Module.finrank_fin_fun]; omega), fun w hw => ?_⟩
  -- Away from `w₀` the first coefficient is negative and the second positive.
  rw [_root_.QuadraticForm.anisotropic_atRealPlace_weightedSumSquares_iff c w, not_or]
  refine ⟨fun h => (hneg w hw).not_gt (by simpa [c] using h 0), fun h => ?_⟩
  have h1 := h (Fin.succ ⟨0, by omega⟩)
  simp only [c, Fin.cons_succ, Pi.one_apply, map_one] at h1
  exact h1.not_gt one_pos

end TauCeti.NumberField.QuadraticForm
