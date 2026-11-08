/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.FiniteBilinearModule.Dyadic.Cyclic
public import TauCeti.LinearAlgebra.FiniteBilinearModule.Dyadic.RankTwo.Basic
public import TauCeti.LinearAlgebra.FiniteBilinearModule.Pi
import TauCeti.LinearAlgebra.FiniteBilinearModule.Dyadic.Relations
import TauCeti.LinearAlgebra.FiniteBilinearModule.Dyadic.Classification
import TauCeti.LinearAlgebra.QuadraticForm.Prod

/-!
# Plane normal forms for equal-exponent dyadic cyclic sums

An orthogonal sum of odd cyclic dyadic generators at one exponent can be reduced to at most
two cyclic generators and a family of standard `u` or `v` dyadic planes. This separates the
cyclic part from the even binary part when comparing decompositions of finite quadratic modules.
It does not classify the resulting plane families or compare decompositions at different scales.

The ternary step combines Nikulin's existing binary and ternary relations. Two of three odd
coefficients agree modulo four; a simultaneous multiplication by five makes them agree modulo
eight, so the repeated-coefficient ternary relation applies. The remaining cyclic coefficient is
congruent modulo eight to the sum of the original coefficients.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*,
  Proposition 1.8.2, including the finite-form transfer clause (k).
* C. T. C. Wall, *Quadratic forms on finite groups, and related topics*, Topology 2 (1963),
  281–298.
-/

public section

namespace TauCeti.FiniteQuadraticModule

private theorem exists_isometry_repeated_cyclic_plane (k : ℕ) [NeZero k] {a c : ℤ}
    (ha : Odd a) (hc : Odd c) :
    ∃ δ : Bool, Nonempty (Isometry
      (((dyadicCyclic k a).prod (dyadicCyclic k a)).prod (dyadicCyclic k c))
      ((if δ then dyadicV k else dyadicU k).prod (dyadicCyclic k (a + a + c)))) := by
  by_cases hmod : a ≡ c [ZMOD 4]
  · have hsum : -5 * c ≡ a + a + c [ZMOD 8] := by
      rcases Int.modEq_iff_dvd.mp hmod with ⟨d, hd⟩
      apply Int.modEq_iff_dvd.mpr
      exact ⟨c - d, by omega⟩
    exact ⟨true, ⟨(dyadicCyclicProdSelfProdIsometryVProdNegFiveMul k ha hmod).trans
      ((QuadraticMap.IsometryEquiv.refl _).prod
        (dyadicCyclicIsometryOfModEqEight k ((by decide : Odd (-5 : ℤ)).mul hc) hsum))⟩⟩
  · have hmod' : a ≡ -c [ZMOD 4] := by
      obtain ⟨s, hs⟩ := ha
      obtain ⟨t, ht⟩ := hc
      simp only [Int.ModEq] at hmod ⊢
      omega
    have hsum : -c ≡ a + a + c [ZMOD 8] := by
      rcases Int.modEq_iff_dvd.mp hmod' with ⟨d, hd⟩
      apply Int.modEq_iff_dvd.mpr
      exact ⟨-d, by omega⟩
    exact ⟨false, ⟨(dyadicCyclicProdSelfProdIsometryUProdNeg k ha hmod').trans
      ((QuadraticMap.IsometryEquiv.refl _).prod
        (dyadicCyclicIsometryOfModEqEight k hc.neg hsum))⟩⟩

private theorem exists_isometry_congr_cyclic_plane (k : ℕ) [NeZero k] {a b c : ℤ}
    (ha : Odd a) (hb : Odd b) (hc : Odd c) (hab : a ≡ b [ZMOD 4]) :
    ∃ δ : Bool, Nonempty (Isometry
      (((dyadicCyclic k a).prod (dyadicCyclic k b)).prod (dyadicCyclic k c))
      ((if δ then dyadicV k else dyadicU k).prod (dyadicCyclic k (a + b + c)))) := by
  have step {b' c' : ℤ} (hb' : Odd b') (hc' : Odd c')
      (hba : b' ≡ a [ZMOD 8]) (hs : a + a + c' ≡ a + b + c [ZMOD 8])
      (e : Isometry
        (((dyadicCyclic k a).prod (dyadicCyclic k b)).prod (dyadicCyclic k c))
        (((dyadicCyclic k a).prod (dyadicCyclic k b')).prod (dyadicCyclic k c'))) :
      ∃ δ : Bool, Nonempty (Isometry
        (((dyadicCyclic k a).prod (dyadicCyclic k b)).prod (dyadicCyclic k c))
        ((if δ then dyadicV k else dyadicU k).prod (dyadicCyclic k (a + b + c)))) := by
    obtain ⟨δ, ⟨f⟩⟩ := exists_isometry_repeated_cyclic_plane k ha hc'
    let e' : Isometry
        (((dyadicCyclic k a).prod (dyadicCyclic k b')).prod (dyadicCyclic k c'))
        (((dyadicCyclic k a).prod (dyadicCyclic k a)).prod (dyadicCyclic k c')) :=
      ((QuadraticMap.IsometryEquiv.refl _).prod
      (dyadicCyclicIsometryOfModEqEight k hb' hba)).prod (QuadraticMap.IsometryEquiv.refl _)
    exact ⟨δ, ⟨e.trans (e'.trans (f.trans ((QuadraticMap.IsometryEquiv.refl _).prod
      (dyadicCyclicIsometryOfModEqEight k ((ha.add_odd ha).add_odd hc') hs))))⟩⟩
  by_cases h8 : b ≡ a [ZMOD 8]
  · apply step hb hc h8
      (by simp only [Int.ModEq] at h8 ⊢; omega) (QuadraticMap.IsometryEquiv.refl _)
  · have h5 : 5 * b ≡ a [ZMOD 8] := by
      obtain ⟨s, hs⟩ := ha
      obtain ⟨t, ht⟩ := hb
      have hb8 : b % 8 = 1 ∨ b % 8 = 3 ∨ b % 8 = 5 ∨ b % 8 = 7 := by omega
      simp only [Int.ModEq] at hab h8 ⊢
      rcases hb8 with h | h | h | h <;> omega
    have hs : a + a + 5 * c ≡ a + b + c [ZMOD 8] := by
      obtain ⟨t, ht⟩ := hb
      obtain ⟨u, hu⟩ := hc
      simp only [Int.ModEq] at h5 ⊢
      omega
    let swap := QuadraticMap.IsometryEquiv.prodAssoc (dyadicCyclic k a).quadratic
      (dyadicCyclic k b).quadratic (dyadicCyclic k c).quadratic
    let swap' := QuadraticMap.IsometryEquiv.prodAssoc (dyadicCyclic k a).quadratic
      (dyadicCyclic k (5 * b)).quadratic (dyadicCyclic k (5 * c)).quadratic
    exact step ((by decide : Odd (5 : ℤ)).mul hb) ((by decide : Odd (5 : ℤ)).mul hc) h5 hs
      (swap.trans (((QuadraticMap.IsometryEquiv.refl _).prod
        (dyadicCyclicProdIsometryFiveMul k hb hc)).trans swap'.symm))

/-- Three odd cyclic generators of the same positive exponent split into one dyadic plane and a
cyclic generator whose coefficient is the sum of the original coefficients. -/
theorem exists_isometry_dyadicCyclic_prod_prod_plane (k : ℕ) [NeZero k] {a b c : ℤ}
    (ha : Odd a) (hb : Odd b) (hc : Odd c) :
    ∃ δ : Bool, Nonempty (Isometry
      (((dyadicCyclic k a).prod (dyadicCyclic k b)).prod (dyadicCyclic k c))
      ((if δ then dyadicV k else dyadicU k).prod (dyadicCyclic k (a + b + c)))) := by
  by_cases hab : a ≡ b [ZMOD 4]
  · exact exists_isometry_congr_cyclic_plane k ha hb hc hab
  have swap (a b c : ℤ) : Isometry
      (((dyadicCyclic k a).prod (dyadicCyclic k b)).prod (dyadicCyclic k c))
      (((dyadicCyclic k a).prod (dyadicCyclic k c)).prod (dyadicCyclic k b)) :=
    (QuadraticMap.IsometryEquiv.prodAssoc _ _ _).trans
      (((QuadraticMap.IsometryEquiv.refl _).prod
        (QuadraticMap.IsometryEquiv.prodComm _ _)).trans
          (QuadraticMap.IsometryEquiv.prodAssoc _ _ _).symm)
  by_cases hac : a ≡ c [ZMOD 4]
  · obtain ⟨δ, ⟨e⟩⟩ := exists_isometry_congr_cyclic_plane k ha hc hb hac
    refine ⟨δ, ⟨(swap a b c).trans ?_⟩⟩
    simpa only [add_right_comm a c b] using e
  · have hbc : b ≡ c [ZMOD 4] := by
      obtain ⟨r, hr⟩ := ha
      obtain ⟨s, hs⟩ := hb
      obtain ⟨t, ht⟩ := hc
      simp only [Int.ModEq] at hab hac ⊢
      omega
    obtain ⟨δ, ⟨e⟩⟩ := exists_isometry_congr_cyclic_plane k hb hc ha hbc
    let e' := ((QuadraticMap.IsometryEquiv.prodComm (dyadicCyclic k a).quadratic
      (dyadicCyclic k b).quadratic).prod (QuadraticMap.IsometryEquiv.refl _)).trans (swap b a c)
    refine ⟨δ, ⟨e'.trans ?_⟩⟩
    have hs : b + c + a = a + b + c := by ring
    rw [hs] at e
    exact e

private theorem exists_isometry_split_three_cyclic (k : ℕ) [NeZero k] {n : ℕ}
    (θ : Fin (n + 3) → ℤ) (hθ : ∀ i, Odd (θ i)) :
    ∃ δ : Bool, Nonempty (Isometry (pi fun i ↦ dyadicCyclic k (θ i))
      ((if δ then dyadicV k else dyadicU k).prod
        (pi fun i : Fin (n + 1) ↦ dyadicCyclic k
          ((Fin.cons (θ 0 + θ 1 + θ 2) (fun j : Fin n ↦ θ j.succ.succ.succ) :
            Fin (n + 1) → ℤ) i)))) := by
  let A := dyadicCyclic k (θ 0)
  let B := dyadicCyclic k (θ 1)
  let C := dyadicCyclic k (θ 2)
  let T := pi fun j : Fin n ↦ dyadicCyclic k (θ j.succ.succ.succ)
  let split₀ := QuadraticMap.IsometryEquiv.consPi
    fun i : Fin (n + 3) ↦ (dyadicCyclic k (θ i)).quadratic
  let split₁ := QuadraticMap.IsometryEquiv.consPi
    fun i : Fin (n + 2) ↦ (dyadicCyclic k (θ i.succ)).quadratic
  let split₂ := QuadraticMap.IsometryEquiv.consPi
    fun i : Fin (n + 1) ↦ (dyadicCyclic k (θ i.succ.succ)).quadratic
  let unpack : Isometry (pi fun i ↦ dyadicCyclic k (θ i)) (((A.prod B).prod C).prod T) :=
    (split₀.symm.trans ((QuadraticMap.IsometryEquiv.refl _).prod
      (split₁.symm.trans ((QuadraticMap.IsometryEquiv.refl _).prod split₂.symm)))).trans
      ((QuadraticMap.IsometryEquiv.prodAssoc A.quadratic B.quadratic
        (C.prod T).quadratic).symm.trans
          (QuadraticMap.IsometryEquiv.prodAssoc (A.prod B).quadratic C.quadratic T.quadratic).symm)
  obtain ⟨δ, ⟨e⟩⟩ := exists_isometry_dyadicCyclic_prod_prod_plane k (hθ 0) (hθ 1) (hθ 2)
  let pack := QuadraticMap.IsometryEquiv.consPi
    fun i : Fin (n + 1) ↦ (dyadicCyclic k
      ((Fin.cons (θ 0 + θ 1 + θ 2) (fun j : Fin n ↦ θ j.succ.succ.succ) :
            Fin (n + 1) → ℤ) i)).quadratic
  exact ⟨δ, ⟨unpack.trans ((e.prod (QuadraticMap.IsometryEquiv.refl _)).trans
    ((QuadraticMap.IsometryEquiv.prodAssoc _ _ _).trans
      ((QuadraticMap.IsometryEquiv.refl _).prod pack)))⟩⟩

private theorem exists_isometry_pi_dyadicCyclic_plane_normal_form_fin (k : ℕ) [NeZero k] {n : ℕ}
    (θ : Fin n → ℤ) (hθ : ∀ i, Odd (θ i)) :
    ∃ (m r : ℕ) (δ : Fin m → Bool) (η : Fin r → ℤ),
      r ≤ 2 ∧ n = 2 * m + r ∧ (∀ i, Odd (η i)) ∧
      Nonempty (Isometry (pi fun i ↦ dyadicCyclic k (θ i))
        ((pi fun i ↦ if δ i then dyadicV k else dyadicU k).prod
          (pi fun i ↦ dyadicCyclic k (η i)))) := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    by_cases hn : n ≤ 2
    · refine ⟨0, n, Fin.elim0, θ, hn, by omega, hθ, ?_⟩
      exact ⟨(QuadraticMap.IsometryEquiv.uniqueProd _ _).symm⟩
    · obtain ⟨n, rfl⟩ : ∃ t, n = t + 3 := ⟨n - 3, by omega⟩
      let θ' : Fin (n + 1) → ℤ :=
        Fin.cons (θ 0 + θ 1 + θ 2) (fun j : Fin n ↦ θ j.succ.succ.succ)
      have hθ' : ∀ i, Odd (θ' i) := by
        intro i
        cases i using Fin.cases with
        | zero => exact ((hθ 0).add_odd (hθ 1)).add_odd (hθ 2)
        | succ j => exact hθ j.succ.succ.succ
      obtain ⟨m, r, δ, η, hr, hn, hη, ⟨e⟩⟩ := ih (n + 1) (by omega) θ' hθ'
      obtain ⟨d, ⟨f⟩⟩ := exists_isometry_split_three_cyclic k θ hθ
      refine ⟨m + 1, r, Fin.cons d δ, η, hr, by omega, hη, ?_⟩
      -- Fix the actual dependent plane carriers before applying the finite-sum equivalence.
      let P : Fin (m + 1) → FiniteQuadraticModule :=
        fun i ↦ if (Fin.cons d δ : Fin (m + 1) → Bool) i then dyadicV k else dyadicU k
      let pack := QuadraticMap.IsometryEquiv.consPi
        (M := fun i ↦ (P i).carrier) fun i ↦ (P i).quadratic
      exact ⟨f.trans (((QuadraticMap.IsometryEquiv.refl _).prod e).trans
        ((QuadraticMap.IsometryEquiv.prodAssoc _ _ _).symm.trans
          (pack.prod (QuadraticMap.IsometryEquiv.refl _))))⟩

/-- An orthogonal sum of odd cyclic generators at a fixed positive exponent is isometric to an
orthogonal sum of dyadic planes and at most two odd cyclic generators. If there are `m` planes and
`r` cyclic generators in the result, then the original number of cyclic generators is `2m + r`.
The Boolean value `true` selects `v(2^k)` and `false` selects `u(2^k)`. -/
theorem exists_isometry_pi_dyadicCyclic_plane_normal_form {ι : Type*} [Fintype ι]
    (k : ℕ) [NeZero k] (θ : ι → ℤ) (hθ : ∀ i, Odd (θ i)) :
    ∃ (m r : ℕ) (δ : Fin m → Bool) (η : Fin r → ℤ),
      r ≤ 2 ∧ Fintype.card ι = 2 * m + r ∧ (∀ i, Odd (η i)) ∧
      Nonempty (Isometry (pi fun i ↦ dyadicCyclic k (θ i))
        ((pi fun i ↦ if δ i then dyadicV k else dyadicU k).prod
          (pi fun i ↦ dyadicCyclic k (η i)))) := by
  classical
  let e := (Fintype.equivFin ι).symm
  obtain ⟨m, r, δ, η, hr, hn, hη, ⟨f⟩⟩ :=
    exists_isometry_pi_dyadicCyclic_plane_normal_form_fin k (θ ∘ e) (fun i ↦ hθ (e i))
  let reindex := QuadraticMap.IsometryEquiv.piCongrLeft
    (fun i ↦ (dyadicCyclic k (θ i)).quadratic) e
  exact ⟨m, r, δ, η, hr, hn, hη, ⟨reindex.symm.trans f⟩⟩

end TauCeti.FiniteQuadraticModule
