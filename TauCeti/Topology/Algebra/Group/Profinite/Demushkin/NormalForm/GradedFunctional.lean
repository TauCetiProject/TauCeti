/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.NormalForm.Kernel.Span
public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.NormalForm.Prescription
public import TauCeti.Topology.Algebra.Group.Profinite.Free.Prescription
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.CrossedHom

/-!
# The graded functionals of the orientation cut out the image of `δ` in `gr(X)`

Let `F = freeProP p (Fin n)` with `n` even, let `r = x₁^q (x₁, x₂)(x₃, x₄) ⋯ (x_{n-1}, x_n)` be
the normal-form word `TauCeti.demushkinWordNeTwo q n` on the generators of `F` with `p ∣ q`, and
let `ρ ∈ gr_1(F)` be its class. Let `χ : F → ℤ_pˣ` be a continuous character with the values of
the orientation of this normal form, `χ(x₂) (1 - q) = 1` and `χ(x_i) = 1` for `i ≠ 2`, and let
`X` be the kernel of the exponent sum at `x₂`, with graded pieces `gr_m(X) ≤ gr_m(F)`. Since `χ`
is trivial on the generators `x_i`, `i ≠ 2`, which topologically generate `X` as a normal subgroup,
`X ≤ ker χ` (`ContinuousMonoidHom.exponentSumKer_le_ker`); for the orientation itself, where
`χ(x₂)` has infinite order, `X` is the kernel of `χ`, Labute's `X = ker χ`. Throughout, indices
in the Lean statements are the `0`-based indices of `Fin n`, so `x₂` is `of ⟨1, _⟩` and `X` is
`TauCeti.freeProP.exponentSumKer p (Fin n) ⟨1, _⟩`.

The constrained span statement of `Demushkin/NormalForm/Kernel/Span.lean` (Labute's Lemma 3) writes
every class of `gr_{m+1}(X)` as `δ_ρ(ω) + Σ_{i ≠ 2} c_i π^{m+1} ξ_i` with `ω ∈ gr_m(X)^n`. This
file supplies the functionals that read off the coefficients `c_i`, and so cuts the image of the
basis-modification map `δ_ρ` out of `gr_{m+1}(X)`. They are the graded functionals
`Δ_{m+1}(D_i) : gr_{m+1}(F) → 𝔽_p` (`TauCeti.IsCrossedHom.gradedFunctional`) of the crossed
homomorphisms `D_i : F → ℤ_p` for `χ` with `D_i(x_j) = δ_{ij}` (`TauCeti.freeProP.crossedHom`):

* on the `p`-power `π^{m+1} ξ_j` with `j ≠ 2`, `Δ_{m+1}(D_i)` takes the value `δ_{ij}`, because
  `χ(x_j) = 1` (`TauCeti.IsCrossedHom.gradedFunctional_gradedPowIter_gradedMkZero`);
* on `δ_ρ(ω)` with `ω ∈ gr_m(X)^n` every `Δ_{m+1}(D)` vanishes
  (`TauCeti.freeProP.gradedFunctional_basisModificationDelta_demushkinWordNeTwo_eq_zero`):
  `δ_ρ(ω)` is the class of `r⁻¹ · θ_w(r)` for a basis modification `θ_w : x_i ↦ x_i w_i` with
  `w_i ∈ X ≤ ker χ`, and a crossed homomorphism for `χ` kills both `r` and `θ_w(r)`, since `χ`
  takes the same values on the tuple `(x_i w_i)` as on `(x_i)` and at those values the word is
  killed (`TauCeti.IsCrossedHom.map_demushkinWordNeTwo_eq_zero`).

Hence a class of `gr_{m+1}(X)` lies in `δ_ρ(gr_m(X)^n)` exactly when it is killed by every
`Δ_{m+1}(D_i)` with `i ≠ 2`
(`TauCeti.freeProP.mem_map_basisModificationDelta_iff_forall_gradedFunctional_crossedHom_eq_zero`).
This is Labute's Lemma 4. At `p = 2` and `q = 2 + 2^f` with `f ≥ 2`, `χ` is the orientation of the
Demushkin relator `x₁^{2+2^f} (x₁, x₂)(x₃, x₄) ⋯` with image `U^[f]`, and the lemma is the finite
step of the successive approximation proving that every Demushkin group with these invariants has a
basis in which its relator is exactly this word: the deviation of the relator from the word, once it
lies in `gr_{m+1}(X)` and is killed by all crossed homomorphisms of `F` into `ℤ_p`, is removed by a
basis correction inside `X`.

## Main results

* `TauCeti.IsCrossedHom.map_apply_demushkinWordNeTwo_eq_zero`: a crossed homomorphism for `χ`
  kills `φ(r)` for every endomorphism `φ` preserving the values of `χ` on the generators.
* `TauCeti.IsCrossedHom.map_inv_mul_basisModification_demushkinWordNeTwo_eq_zero`: a crossed
  homomorphism for `χ` kills `r⁻¹ · θ_w(r)` for every basis modification by elements of `ker χ`.
* `TauCeti.freeProP.gradedFunctional_basisModificationDelta_demushkinWordNeTwo_eq_zero`: the graded
  functional of a crossed homomorphism for `χ` vanishes on `δ_ρ(gr_m(X)^n)`.
* `TauCeti.freeProP.mem_map_basisModificationDelta_iff_forall_gradedFunctional_crossedHom_eq_zero`:
  **a class of `gr_{m+1}(X)` lies in `δ_ρ(gr_m(X)^n)` exactly when the graded functionals of the
  `D_i`, `i ≠ 2`, kill it.**

## References

* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), 106–132, §4,
  Lemma 4 and the proof of Theorem 5.
-/

public section

namespace TauCeti

open Subgroup Submodule

variable {p : ℕ} [Fact p.Prime] {n q : ℕ} {χ : freeProP p (Fin n) →ₜ* ℤ_[p]ˣ}

/-- **A crossed homomorphism for the orientation kills the image of the normal-form word under an
endomorphism preserving the character values on the generators**: for `χ` with `χ(x₂) (1 - q) = 1`
and `χ(x_i) = 1` for `i ≠ 2`, the word on the tuple `(φ x_i)` is killed at the same character
values. -/
theorem IsCrossedHom.map_apply_demushkinWordNeTwo_eq_zero (hn1 : 1 < n)
    (h₁ : (χ (freeProP.of ⟨1, hn1⟩) : ℤ_[p]) * (1 - q) = 1)
    (h : ∀ j, j ≠ ⟨1, hn1⟩ → χ (freeProP.of j) = 1) {f : freeProP p (Fin n) → ℤ_[p]}
    (hf : IsCrossedHom χ f) (φ : freeProP p (Fin n) →ₜ* freeProP p (Fin n))
    (hφ : ∀ i, χ (φ (freeProPGen p n i)) = χ (freeProPGen p n i)) :
    f (φ (demushkinWordNeTwo q n (freeProPGen p n))) = 0 := by
  rw [TauCeti.map_demushkinWordNeTwo]
  refine hf.map_demushkinWordNeTwo_eq_zero hn1 ?_ fun i hi ↦ ?_
  · rw [Function.comp_apply, hφ, freeProPGen_of_lt p hn1]
    exact h₁
  · rw [Function.comp_apply, hφ]
    by_cases hi' : i < n
    · rw [freeProPGen_of_lt p hi']
      exact h _ fun e ↦ hi (congrArg Fin.val e)
    · rw [freeProPGen_eq_one_of_le p (not_lt.1 hi'), _root_.map_one]

/-- **A crossed homomorphism for the orientation kills the relator moved by a basis modification
inside the kernel of the character.** For `χ` with `χ(x₂) (1 - q) = 1` and `χ(x_i) = 1` for
`i ≠ 2`, a crossed homomorphism `f` for `χ`, and a family `w` of elements of `λ_m(F)` on which `χ`
is trivial (for instance elements of the kernel `X` of the exponent sum at `x₂`, since `X ≤ ker χ`),
`f (r⁻¹ · θ_w(r)) = 0` for `r = x₁^q (x₁, x₂) ⋯ (x_{n-1}, x_n)`: the character takes the same
values on the modified tuple `(x_i w_i)` as on `(x_i)`, and at those values a crossed homomorphism
kills the word. -/
theorem IsCrossedHom.map_inv_mul_basisModification_demushkinWordNeTwo_eq_zero (hn1 : 1 < n)
    (h₁ : (χ (freeProP.of ⟨1, hn1⟩) : ℤ_[p]) * (1 - q) = 1)
    (h : ∀ j, j ≠ ⟨1, hn1⟩ → χ (freeProP.of j) = 1) {f : freeProP p (Fin n) → ℤ_[p]}
    (hf : IsCrossedHom χ f) {m : ℕ} (w : Fin n → pLowerCentralSeries p (freeProP p (Fin n)) m)
    (hw : ∀ i, χ (w i) = 1) :
    f ((demushkinWordNeTwo q n (freeProPGen p n))⁻¹ *
      freeProP.basisModification w (demushkinWordNeTwo q n (freeProPGen p n))) = 0 := by
  -- The values of `χ` on the modified tuple are those on the generator tuple.
  have hθ : ∀ i, χ (freeProP.basisModification w (freeProPGen p n i)) = χ (freeProPGen p n i) :=
    fun i ↦ by
      by_cases hi' : i < n
      · rw [freeProPGen_of_lt p hi', freeProP.basisModification_of, _root_.map_mul, hw, mul_one]
      · rw [freeProPGen_eq_one_of_le p (not_lt.1 hi'), _root_.map_one]
  have hr := hf.map_apply_demushkinWordNeTwo_eq_zero hn1 h₁ h (ContinuousMonoidHom.id _) fun _ ↦ rfl
  rw [ContinuousMonoidHom.coe_id, id_eq] at hr
  rw [hf.map_mul, hf.map_apply_demushkinWordNeTwo_eq_zero hn1 h₁ h _ hθ, mul_zero, zero_add,
    hf.map_inv, hr, mul_zero]

namespace freeProP

/-- **The graded functional of a crossed homomorphism for the orientation vanishes on
`δ_ρ(gr_m(X)^n)`** (Labute, §4, Lemma 4 (2)). For `χ` with `χ(x₂) (1 - q) = 1` and `χ(x_i) = 1` for
`i ≠ 2`, a continuous crossed homomorphism `f` for `χ`, the class `ρ` of
`r = x₁^q (x₁, x₂) ⋯ (x_{n-1}, x_n)` and a family `v` of classes in `gr_m(X)`, where `X` is the
kernel of the exponent sum at `x₂`, `Δ_{m+1}(f) (δ_ρ(v)) = 0`: `δ_ρ(v)` is the class of
`r⁻¹ · θ_w(r)` for a basis modification `θ_w` by elements of `X`, which `f` kills. -/
@[simp]
theorem gradedFunctional_basisModificationDelta_demushkinWordNeTwo_eq_zero (hn1 : 1 < n)
    (hq : p ∣ q) {m : ℕ} (hm : 1 ≤ m) (h₁ : (χ (of ⟨1, hn1⟩) : ℤ_[p]) * (1 - q) = 1)
    (h : ∀ j, j ≠ ⟨1, hn1⟩ → χ (of j) = 1) {f : freeProP p (Fin n) → ℤ_[p]}
    (hf : IsCrossedHom χ f) (hfc : Continuous f)
    {v : Fin n → gradedPiece p (freeProP p (Fin n)) m}
    (hv : ∀ i, v i ∈ gradedPieceOf p (exponentSumKer p (Fin n) ⟨1, hn1⟩) m) :
    hf.gradedFunctional ((isProP_freeProP p (Fin n)).mem_unitsPrincipal_one χ) hfc (m + 1)
      (basisModificationDelta p (Fin n) hm (gradedMk p (freeProP p (Fin n)) 1
        ⟨demushkinWordNeTwo q n (freeProPGen p n),
          demushkinWordNeTwo_mem_pLowerCentralSeries_one hq n _⟩) v) = 0 := by
  choose w hwX hwv using fun i ↦ mem_gradedPieceOf_iff.1 (hv i)
  have hv' : v = fun i ↦ gradedMk p (freeProP p (Fin n)) m (w i) := funext fun i ↦ (hwv i).symm
  rw [hv', ← gradedMk_inv_mul_basisModification hm w, hf.gradedFunctional_gradedMk _ _ _ _ (c := 0)
    (by
      rw [mul_zero]
      exact hf.map_inv_mul_basisModification_demushkinWordNeTwo_eq_zero hn1 h₁ h w fun i ↦
        MonoidHom.mem_ker.1 (χ.exponentSumKer_le_ker h (hwX i))),
    map_zero]

/-- **The image of `δ_ρ` on `gr_m(X)^n` is the common kernel in `gr_{m+1}(X)` of the graded
functionals of the orientation** (Labute, §4, Lemma 4 (4)). Let `n` be even, `p ∣ q`, `ρ` the class
of `x₁^q (x₁, x₂) ⋯ (x_{n-1}, x_n)`, `χ` a continuous character with `χ(x₂) (1 - q) = 1` and
`χ(x_i) = 1` for `i ≠ 2`, and `X` the kernel of the exponent sum at `x₂`. For `m ≥ 1`, a class
`ε ∈ gr_{m+1}(X)` lies in `δ_ρ(gr_m(X)^n)` exactly when `Δ_{m+1}(D_i) ε = 0` for every `i ≠ 2`,
where `D_i` is the crossed homomorphism for `χ` with `D_i(x_j) = δ_{ij}`. -/
theorem mem_map_basisModificationDelta_iff_forall_gradedFunctional_crossedHom_eq_zero (hn : Even n)
    (hn1 : 1 < n) (hq : p ∣ q) {m : ℕ} (hm : 1 ≤ m)
    (h₁ : (χ (of ⟨1, hn1⟩) : ℤ_[p]) * (1 - q) = 1) (h : ∀ j, j ≠ ⟨1, hn1⟩ → χ (of j) = 1)
    {ε : gradedPiece p (freeProP p (Fin n)) (m + 1)}
    (hε : ε ∈ gradedPieceOf p (exponentSumKer p (Fin n) ⟨1, hn1⟩) (m + 1)) :
    ε ∈ (Submodule.pi Set.univ
        fun _ : Fin n ↦ gradedPieceOf p (exponentSumKer p (Fin n) ⟨1, hn1⟩) m).map
      (basisModificationDelta p (Fin n) hm (gradedMk p (freeProP p (Fin n)) 1
        ⟨demushkinWordNeTwo q n (freeProPGen p n),
          demushkinWordNeTwo_mem_pLowerCentralSeries_one hq n _⟩)) ↔
      ∀ i, i ≠ ⟨1, hn1⟩ →
        (isCrossedHom_crossedHom χ (Pi.single i 1)).gradedFunctional
          ((isProP_freeProP p (Fin n)).mem_unitsPrincipal_one χ) (continuous_crossedHom χ _)
          (m + 1) ε = 0 := by
  classical
  constructor
  · rintro ⟨v, hv, rfl⟩ i -
    exact gradedFunctional_basisModificationDelta_demushkinWordNeTwo_eq_zero hn1 hq hm h₁ h _ _
      fun j ↦ Submodule.mem_pi.1 hv j (Set.mem_univ j)
  · intro hΔ
    -- By the constrained span statement, `ε = δ_ρ(v) + Σ_{a ≠ 2} c_a π^{m+1} ξ_a`.
    rw [gradedPieceOf_exponentSumKer_demushkinWordNeTwo_eq_map_basisModificationDelta_sup hn hn1 hq
      hm] at hε
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hε
    obtain ⟨c, rfl⟩ := (mem_span_range_iff_exists_fun (ZMod p)).1 hz
    obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.1 hy
    -- Applying `Δ_{m+1}(D_a)` reads off the coefficient `c_a`, which therefore vanishes.
    have hc : ∀ a : {a : Fin n // a ≠ ⟨1, hn1⟩}, c a = 0 := fun a ↦ by
      have hΔa := hΔ a a.2
      rw [map_add, map_sum, gradedFunctional_basisModificationDelta_demushkinWordNeTwo_eq_zero hn1
        hq hm h₁ h _ _ (fun j ↦ Submodule.mem_pi.1 hv j (Set.mem_univ j)), zero_add,
        Finset.sum_eq_single a (fun b _ hb ↦ ?_) fun hb ↦ (hb (Finset.mem_univ _)).elim] at hΔa
      · rwa [map_smul, IsCrossedHom.gradedFunctional_gradedPowIter_gradedMkZero _ _ _ _ (h a a.2),
          crossedHom_of, Pi.single_eq_same, map_one, smul_eq_mul, mul_one] at hΔa
      · rw [map_smul, IsCrossedHom.gradedFunctional_gradedPowIter_gradedMkZero _ _ _ _ (h b b.2),
          crossedHom_of, Pi.single_eq_of_ne (fun e ↦ hb (Subtype.ext e)), map_zero, smul_zero]
    simp only [hc, zero_smul, Finset.sum_const_zero, add_zero]
    exact Submodule.mem_map_of_mem hv

end freeProP

end TauCeti
