/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.NormalForm.DegreeOneForm
public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.NormalForm.QInvariant
public import TauCeti.Topology.Algebra.Group.Profinite.Free.BracketSpan
public import TauCeti.Topology.Algebra.Group.Profinite.Free.SuccessiveApproximation.Basic

/-!
# The exact normal form when the first exponent is divisible by `p^2`

Let `F = freeProP p (Fin n)` and let `r ∈ λ₁(F)` have exponent vector `q e₁`, where
`p² ∣ q`. If the degree-one form of `r` is nondegenerate and alternating, a continuous
automorphism of `F` carries `r` to

`x₁^q (x₁, x₂) (x₃, x₄) ⋯ (x_{n-1}, x_n)`.

The degree-one change of basis fixes `x₁`, and therefore preserves the exponent vector of `r`.
After that change of basis the two relators agree modulo `λ₂(F)`. Their discrepancy lies in the
closed commutator subgroup. The pivot-constrained span theorem
`TauCeti.freeProP.exists_apply_mem_commutator_basisModificationDelta_eq_of_mem_range` supplies
basis corrections that still preserve the exponent vector, so the relative successive-
approximation theorem makes the congruence an equality.

This is the `q ≠ p` part of Labute's normal-form argument. In particular, at `p = 2` it is the
normalization used on the even-rank tail relator in the proof of the odd-rank dyadic form.

## Main result

* `TauCeti.freeProP.exists_continuousMulEquiv_apply_eq_demushkinWordNeTwo_of_sq_dvd`: a relator
  with exponent vector `q e₁`, `p² ∣ q`, and nondegenerate alternating degree-one form is
  carried exactly to the `q ≠ p` normal-form word.

## References

* J. P. Labute, *Classification of Demushkin groups*, Canadian J. Math. 19 (1967), §3,
  Proposition 5 and the proof of Theorem 3.
-/

public section

namespace TauCeti.freeProP

open Subgroup Submodule

variable {p n q : ℕ} [Fact p.Prime]

/-- A change of basis fixing the first generator preserves an exponent vector supported there. -/
private theorem exponentSum_apply_eq_of_apply_freeProPGen_zero_eq
    (hn : 0 < n) (r : freeProP p (Fin n)) (e : freeProP p (Fin n) ≃ₜ* freeProP p (Fin n))
    (he : e (freeProPGen p n 0) = freeProPGen p n 0)
    (hv : ∀ k : Fin n, (exponentSum p (Fin n) r).toAdd k =
      if (k : ℕ) = 0 then (q : ℤ_[p]) else 0) :
    exponentSum p (Fin n) (e r) = exponentSum p (Fin n) r := by
  let i₀ : Fin n := ⟨0, hn⟩
  have hx₀ : freeProPGen p n 0 = of i₀ := freeProPGen_of_lt p hn
  have he' : (e : freeProP p (Fin n) →ₜ* freeProP p (Fin n)) (freeProPGen p n 0) =
      freeProPGen p n 0 := he
  have hsingle : (exponentSum p (Fin n) r).toAdd = Pi.single i₀ (q : ℤ_[p]) := by
    funext k
    rw [hv k, Pi.single_apply]
    by_cases hk : k = i₀
    · subst k
      simp [i₀]
    · have hk' : (k : ℕ) ≠ 0 := fun h ↦ hk (Fin.ext h)
      simp [hk, hk']
  apply Multiplicative.toAdd.injective
  rw [hsingle]
  have h := apply_eq_prod_padicPow_exponentSum p (Fin n)
    (isProP_multiplicative_pi_padicInt p (Fin n))
    ((exponentSum p (Fin n)).comp
      (e : freeProP p (Fin n) →ₜ* freeProP p (Fin n))) r
  rw [ContinuousMonoidHom.coe_comp, Function.comp_apply] at h
  have h' := congrArg Multiplicative.toAdd h
  rw [toAdd_prod] at h'
  have h'' : (exponentSum p (Fin n) (e r)).toAdd =
      ∑ i, Multiplicative.toAdd ((isProP_multiplicative_pi_padicInt p (Fin n)).padicPow
        (((exponentSum p (Fin n)).comp
          (e : freeProP p (Fin n) →ₜ* freeProP p (Fin n))) (of i))
        ((exponentSum p (Fin n) r).toAdd i)) := by
    simpa using h'
  rw [h'']
  classical
  rw [Finset.sum_eq_single i₀]
  · rw [hsingle, Pi.single_eq_same, ContinuousMonoidHom.coe_comp, Function.comp_apply,
      ← hx₀, he', hx₀, exponentSum_of]
    rw [IsProP.padicPow_ofAdd_pi, toAdd_ofAdd, ← Pi.single_smul, smul_eq_mul, mul_one]
  · intro k _ hk
    rw [hsingle, Pi.single_eq_of_ne hk, IsProP.padicPow_zero, toAdd_one]
  · simp

/-- **Labute's exact normal form when `p² ∣ q`.** Let `r ∈ λ₁(F)` be a relator of the free
pro-`p` group on `n > 0` generators. Suppose its exponent vector is `q e₁`, where `p² ∣ q`,
and its degree-one form is nondegenerate and alternating. Then a continuous automorphism of `F`
carries `r` to `x₁^q (x₁, x₂)(x₃, x₄) ⋯ (x_{n-1}, x_n)`. -/
theorem exists_continuousMulEquiv_apply_eq_demushkinWordNeTwo_of_sq_dvd
    (hn : 0 < n) (r : pLowerCentralSeries p (freeProP p (Fin n)) 1)
    (hnd : (degreeOneForm (gradedMk p (freeProP p (Fin n)) 1 r)).Nondegenerate)
    (halt : (degreeOneForm (gradedMk p (freeProP p (Fin n)) 1 r)).IsAlt)
    (hq : p ^ 2 ∣ q)
    (hv : ∀ k : Fin n, (exponentSum p (Fin n) (r : freeProP p (Fin n))).toAdd k =
      if (k : ℕ) = 0 then (q : ℤ_[p]) else 0) :
    ∃ e : freeProP p (Fin n) ≃ₜ* freeProP p (Fin n),
      e r = demushkinWordNeTwo q n (freeProPGen p n) := by
  have hpq : p ∣ q := (dvd_pow_self p two_ne_zero).trans hq
  obtain ⟨hneven, e₁, he₁, hcong⟩ :=
    exists_continuousMulEquiv_freeProPGen_zero_eq_inv_mul_demushkinWordNeTwo_mem
      r hnd halt hpq hv
  let s : pLowerCentralSeries p (freeProP p (Fin n)) 1 :=
    ⟨e₁ r, e₁.toMonoidHom.map_pLowerCentralSeries_le e₁.continuous 1 ⟨r, r.2, rfl⟩⟩
  let w : pLowerCentralSeries p (freeProP p (Fin n)) 1 :=
    ⟨demushkinWordNeTwo q n (freeProPGen p n),
      demushkinWordNeTwo_mem_pLowerCentralSeries_one hpq n _⟩
  have hclass : gradedMk p (freeProP p (Fin n)) 1 s =
      gradedMk p (freeProP p (Fin n)) 1 w := by
    rw [gradedMk_eq_gradedMk_iff, QuotientGroup.eq]
    exact hcong
  have hsum : exponentSum p (Fin n) (s : freeProP p (Fin n)) =
      exponentSum p (Fin n) (w : freeProP p (Fin n)) := by
    rw [exponentSum_apply_eq_of_apply_freeProPGen_zero_eq hn r e₁ he₁ hv]
    apply Multiplicative.toAdd.injective
    rw [toAdd_exponentSum_demushkinWordNeTwo]
    funext k
    rw [hv k, freeProPGen_of_lt p hn, exponentSum_of, toAdd_ofAdd, Pi.smul_apply,
      Pi.single_apply]
    by_cases hk : (k : ℕ) = 0
    · have : k = ⟨0, hn⟩ := Fin.ext hk
      subst k
      simp
    · have hk' : k ≠ ⟨0, hn⟩ := fun h ↦ hk (congrArg Fin.val h)
      simp [hk, hk']
  have hspan : span (ZMod p) (Set.range fun i ↦
      degreeOneDeriv p (Fin n) i (gradedMk p (freeProP p (Fin n)) 1 s)) = ⊤ := by
    rw [span_range_degreeOneDeriv_eq_top_iff_nondegenerate_degreeOneForm, hclass]
    exact nondegenerate_degreeOneForm_demushkinWordNeTwo hneven hpq
  have hc : ∀ i, (degreeOneBasis p (Fin n)).repr
      (gradedMk p (freeProP p (Fin n)) 1 s) (Sum.inl i) = 0 := by
    intro i
    rw [hclass, degreeOneBasis_repr_gradedMk_demushkinWordNeTwo_inl hpq]
    split_ifs
    · exact (ZMod.natCast_eq_zero_iff (q / p) p).2
        ((Nat.dvd_div_iff_mul_dvd hpq).2 (by simpa [pow_two] using hq))
    · rfl
  have hrelative : ∀ m (hm : 1 ≤ m),
      ∀ z : pLowerCentralSeries p (freeProP p (Fin n)) (m + 1),
        (z : freeProP p (Fin n)) ∈ (commutator (freeProP p (Fin n))).topologicalClosure →
          ∃ ω : Fin n → pLowerCentralSeries p (freeProP p (Fin n)) m,
            (∀ i, (exponentSum p (Fin n) (s : freeProP p (Fin n))).toAdd i ≠ 0 →
              (ω i : freeProP p (Fin n)) ∈
                (commutator (freeProP p (Fin n))).topologicalClosure) ∧
            basisModificationDelta p (Fin n) hm
                (gradedMk p (freeProP p (Fin n)) 1 s)
                (fun i ↦ gradedMk p (freeProP p (Fin n)) m (ω i)) =
              gradedMk p (freeProP p (Fin n)) (m + 1) z := by
    intro m hm z hz
    have hy := gradedMk_mem_range_basisModificationDelta_of_mem_topologicalClosure_commutator
      hm hspan hc z hz
    let i₀ : Fin n := ⟨0, hn⟩
    obtain ⟨ω, hω₀, hω⟩ :=
      exists_apply_mem_commutator_basisModificationDelta_eq_of_mem_range
        hm hspan hc i₀ hy
    refine ⟨ω, ?_, hω⟩
    intro i hi
    have hi₀ : i = i₀ := by
      by_contra hne
      apply hi
      rw [exponentSum_apply_eq_of_apply_freeProPGen_zero_eq hn r e₁ he₁ hv]
      rw [hv i]
      have hi_ne : (i : ℕ) ≠ 0 := fun h ↦ hne (Fin.ext h)
      simp [hi_ne]
    subst i
    exact subset_closure hω₀
  obtain ⟨e₂, he₂⟩ :=
    exists_continuousMulEquiv_apply_eq_of_exponentSum_eq s w hclass hsum hrelative
  exact ⟨e₁.trans e₂, by simpa [ContinuousMulEquiv.trans_apply, s, w] using he₂⟩

end TauCeti.freeProP
