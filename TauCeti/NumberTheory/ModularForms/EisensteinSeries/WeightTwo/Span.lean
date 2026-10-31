/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.EisensteinSeries.WeightTwo.Primitive
import TauCeti.NumberTheory.ModularForms.EisensteinSeries.GammaSet

/-!
# Every weighted weight-two series is Eisenstein

The primitive weight-two Eisenstein subspace of `M₂(Γ(N))`
(`TauCeti.EisensteinSeries.primitiveG2Subspace`) consists of the series `G₂^W`
(`TauCeti.EisensteinSeries.weightedG2MF`) whose weights `W` are supported on the residues of
coprime pairs and have total mass zero. This file proves that it contains `G₂^W` for every weight
`W : (Fin 2 → ZMod N) → ℂ`, so that it is the span of all the weighted series. This is the
weight-two counterpart of
`TauCeti.EisensteinSeries.weightedEisensteinSeriesMF_mem_primitiveEisensteinSubspace`.

In weight `k ≥ 3` the inclusion follows by sorting the lattice points by their gcd. In weight two
the series only converge in blocks, and the argument runs instead through the division values of
`℘` and three facts from `TauCeti.NumberTheory.ModularForms.EisensteinSeries.WeightTwo.Weighted`.

* *Level one.* A weight invariant under `SL(2, ℤ)` gives a level-one modular form of weight two,
  hence `0` (`TauCeti.EisensteinSeries.weightedG2_eq_zero_of_forall_vecMul_eq`). Applied to the
  indicator of the residues of coprime pairs, this removes the mass condition: `G₂^W` is primitive
  for every `W` supported on these residues.
* *Change of level.* For `M ∣ N`, the series of `W` modulo `M` and of `c ↦ W(c mod M)` modulo
  `N` agree (`TauCeti.EisensteinSeries.weightedG2_comp_castHom`). For `W` of mass zero, the
  blocks of residues modulo `N` are unions of blocks modulo `M`; constant weights have the zero
  series at every level.
* *Common division points.* If `c = g e` with `N = g M`, the series of the single residues `c`
  modulo `N` and `e` modulo `M` agree up to `g²`
  (`TauCeti.EisensteinSeries.weightedG2_single_eq_of_val_eq`).

For a prime `p` with `N = M p` and a weight `W` modulo `M` supported on the residues of coprime
pairs, the lift `c ↦ W(c mod M)` is supported on residues of coprime pairs, except at the residues
`p e`, which contribute `p⁻²` times the series of `e ↦ W(p e)`. If `p ∣ M` this weight is zero.
Otherwise multiplication by `p` has finite order `r` on `(ℤ/M)²`, and iterating gives
`(1 - p^{-2r}) G₂^W` primitive modulo `N`. Raising the level one prime at a time, the same holds
for every `M ∣ N`.
Finally, a residue `a` modulo `N` is `g e` with `g = gcd(a₀, a₁, N)` and `e` the residue of a
coprime pair modulo `N / g`.

## Main results

* `TauCeti.EisensteinSeries.weightedG2MF_mem_primitiveG2Subspace`: every series `G₂^W` lies in
  the primitive weight-two Eisenstein subspace.
* `TauCeti.EisensteinSeries.range_weightedG2MFₗ`: the primitive weight-two Eisenstein subspace is
  the span of all the series `G₂^W`.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005], §4.2 and
  §4.6, where the weight-two Eisenstein series of level `N` are constructed by Hecke's trick.
-/

public noncomputable section

open Matrix Matrix.SpecialLinearGroup ModularForm CongruenceSubgroup UpperHalfPlane
open _root_.EisensteinSeries
open scoped MatrixGroups

namespace TauCeti.EisensteinSeries

variable {N : ℕ} [NeZero N]

/-- The series of a weight supported on the residues of coprime pairs lies in the primitive
weight-two Eisenstein subspace, whatever its total mass. -/
private lemma weightedG2MF_mem_primitiveG2Subspace_of_support {W : (Fin 2 → ZMod N) → ℂ}
    (hW : ∀ a, W a ≠ 0 → Nonempty (gammaSet N 1 a)) :
    weightedG2MF W ∈ primitiveG2Subspace N := by
  classical
  -- the indicator of the residues of coprime pairs is `SL(2, ℤ)`-invariant, so its series is `0`
  let S : (Fin 2 → ZMod N) → ℂ := fun a ↦ if Nonempty (gammaSet N 1 a) then 1 else 0
  have hS0 : weightedG2 S = 0 := weightedG2_eq_zero_of_forall_vecMul_eq fun γ a ↦ by
    have h : Nonempty (gammaSet N 1 (a ᵥ* ((γ : SL(2, ZMod N)) :
        Matrix (Fin 2) (Fin 2) (ZMod N)))) ↔ Nonempty (gammaSet N 1 a) :=
      ⟨fun ⟨x⟩ ↦ ⟨(gammaSetEquiv _ γ).symm x⟩, fun ⟨x⟩ ↦ ⟨gammaSetEquiv _ γ x⟩⟩
    simp only [S, h]
  have hS : weightedG2MF S = 0 :=
    DFunLike.coe_injective (by rw [coe_weightedG2MF, hS0, FunLike.coe_zero])
  have hm : (∑ a, S a) ≠ 0 := by
    have h01 : Nonempty (gammaSet N 1 ((↑) ∘ (![0, 1] : Fin 2 → ℤ))) :=
      ⟨⟨![0, 1], rfl, by simp⟩⟩
    simp only [S]
    rw [Finset.sum_boole]
    exact Nat.cast_ne_zero.mpr
      (Finset.card_ne_zero.mpr ⟨_, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h01⟩⟩)
  -- `(∑ S) W - (∑ W) S` is supported on the residues of coprime pairs and has mass zero
  have hV : (∑ a, S a) • W - (∑ a, W a) • S ∈ primitiveG2Weights N := by
    refine mem_primitiveG2Weights_iff.mpr ⟨fun a ha ↦ ?_, ?_⟩
    · by_contra h
      have hWa : W a = 0 := by_contra fun hWa ↦ h (hW a hWa)
      exact ha (by simp only [Pi.sub_apply, Pi.smul_apply, S, ite_eq_right h, hWa]; simp)
    · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_sub_distrib,
        ← Finset.mul_sum]
      ring
  have hsum : weightedG2MF W =
      (∑ a, S a)⁻¹ • weightedG2MF ((∑ a, S a) • W - (∑ a, W a) • S) := by
    simp only [← weightedG2MFₗ_apply, map_sub, map_smul]
    simp [hS, smul_smul, hm]
  rw [hsum]
  exact Submodule.smul_mem _ _ (mem_primitiveG2Subspace_iff.mpr ⟨_, hV, rfl⟩)

/-! ### The functions of the primitive weight-two Eisenstein subspace -/

variable {M : ℕ} [NeZero M]

variable (N) in
/-- The functions underlying the primitive weight-two Eisenstein subspace. -/
private def g2Span : Submodule ℂ (ℍ → ℂ) := (primitiveG2Weights N).map (weightedG2ₗ N)

private lemma weightedG2_mem_g2Span_iff (W : (Fin 2 → ZMod N) → ℂ) :
    weightedG2 W ∈ g2Span N ↔ weightedG2MF W ∈ primitiveG2Subspace N := by
  refine ⟨fun ⟨W', hW', h⟩ ↦ mem_primitiveG2Subspace_iff.mpr ⟨W', hW', DFunLike.coe_injective (by
    rw [coe_weightedG2MF, coe_weightedG2MF, ← h, weightedG2ₗ_apply])⟩, fun h ↦ ?_⟩
  obtain ⟨W', hW', h'⟩ := mem_primitiveG2Subspace_iff.mp h
  exact ⟨W', hW', by rw [weightedG2ₗ_apply, ← coe_weightedG2MF, h', coe_weightedG2MF]⟩

/-- **Removing the residues divisible by a prime.** For a prime `p`, `N = M p` and a weight `W`
modulo `M` supported on the residues of coprime pairs, the series of `W` is that of
`c ↦ W(c mod M)` of level `N`. The residues `c = p e` contribute `p⁻²` times the series of
`e ↦ W(p e)` of level `M`, and all other residues `c` with `W(c mod M) ≠ 0` are residues of
coprime pairs. -/
private lemma weightedG2_sub_mem_g2Span {p : ℕ} (hp : p.Prime) (hNM : N = M * p)
    {W : (Fin 2 → ZMod M) → ℂ} (hW : ∀ e, W e ≠ 0 → Nonempty (gammaSet M 1 e)) :
    weightedG2 W - ((p : ℂ) ^ 2)⁻¹ • weightedG2 (fun e ↦ W ((p : ZMod M) • e)) ∈ g2Span N := by
  classical
  have h : M ∣ N := ⟨p, hNM⟩
  let π : (Fin 2 → ZMod N) → (Fin 2 → ZMod M) := fun c ↦ ZMod.castHom h (ZMod M) ∘ c
  -- the residues `p e` modulo `N`
  let ι : (Fin 2 → ZMod M) → (Fin 2 → ZMod N) := fun e i ↦ ((p * (e i).val : ℕ) : ZMod N)
  have hval (e : Fin 2 → ZMod M) (i : Fin 2) : (ι e i).val = p * (e i).val :=
    ZMod.val_natCast_of_lt (by
      rw [hNM, mul_comm M]
      exact Nat.mul_lt_mul_of_pos_left (e i).val_lt hp.pos)
  have hπι (e : Fin 2 → ZMod M) : π (ι e) = (p : ZMod M) • e := by
    ext i
    simp only [π, ι, Function.comp_apply, Nat.cast_mul, map_mul, map_natCast,
      ZMod.natCast_zmod_val, Pi.smul_apply, smul_eq_mul]
  have hinj : Function.Injective ι := fun e e' hee' ↦ funext fun i ↦ ZMod.val_injective M
    (Nat.eq_of_mul_eq_mul_left hp.pos (by rw [← hval, ← hval, hee']))
  let Wp : (Fin 2 → ZMod N) → ℂ := ∑ e, W ((p : ZMod M) • e) • Pi.single (ι e) 1
  have hWp_apply (e : Fin 2 → ZMod M) : Wp (ι e) = W ((p : ZMod M) • e) := by
    simp only [Wp, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, hinj.eq_iff,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  have hWp_apply' {c : Fin 2 → ZMod N} (hc : ∀ e, ι e ≠ c) : Wp c = 0 := by
    simp only [Wp, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_eq_zero fun e _ ↦ by rw [Pi.single_eq_of_ne (hc e).symm, mul_zero]
  have hWp : weightedG2 Wp = ((p : ℂ) ^ 2)⁻¹ • weightedG2 (fun e ↦ W ((p : ZMod M) • e)) := by
    rw [weightedG2_eq_sum_single (fun e ↦ W ((p : ZMod M) • e)), Finset.smul_sum,
      ← weightedG2ₗ_apply, map_sum]
    refine Finset.sum_congr rfl fun e _ ↦ ?_
    rw [map_smul, weightedG2ₗ_apply, weightedG2_single_eq_of_val_eq (by rw [hNM, mul_comm])
      (hval e), smul_comm]
  -- the remaining residues are those of coprime pairs
  let Wπ : (Fin 2 → ZMod N) → ℂ := fun c ↦ W (π c)
  have hWπ (c : Fin 2 → ZMod N) : Wπ c = W (π c) := rfl
  have hsupp (c : Fin 2 → ZMod N) (hc : (Wπ - Wp) c ≠ 0) : Nonempty (gammaSet N 1 c) := by
    rw [Pi.sub_apply, hWπ] at hc
    by_cases hι : ∃ e, ι e = c
    · obtain ⟨e, rfl⟩ := hι
      exact (hc (by rw [hWp_apply, hπι, sub_self])).elim
    push Not at hι
    rw [hWp_apply' hι, sub_zero] at hc
    have hM : Nat.Coprime ((c 0).val.gcd (c 1).val) M := by
      have hπc : ((↑) : ℤ → ZMod M) ∘ (fun i ↦ ((c i).val : ℤ)) = π c := by
        ext i
        simp only [Function.comp_apply, π, Int.cast_natCast, ZMod.castHom_apply,
          ZMod.cast_eq_val]
      have h1 := hW _ hc
      rw [← hπc, nonempty_gammaSet_intCast_iff, Int.gcd_natCast_natCast] at h1
      exact h1
    have hpc : Nat.Coprime ((c 0).val.gcd (c 1).val) p := by
      refine Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr fun hpd ↦ ?_)
      have hdvd (i : Fin 2) : p ∣ (c i).val := by
        fin_cases i
        exacts [hpd.trans (Nat.gcd_dvd_left _ _), hpd.trans (Nat.gcd_dvd_right _ _)]
      refine hι (fun i ↦ (((c i).val / p : ℕ) : ZMod M)) (funext fun i ↦ ZMod.val_injective N ?_)
      refine (hval (fun i ↦ (((c i).val / p : ℕ) : ZMod M)) i).trans ?_
      rw [ZMod.val_natCast_of_lt, Nat.mul_div_cancel' (hdvd i)]
      exact (Nat.div_lt_iff_lt_mul hp.pos).mpr (hNM ▸ (c i).val_lt)
    have hcop := Nat.Coprime.mul_right hM hpc
    rw [← hNM] at hcop
    exact (nonempty_gammaSet_iff_coprime_val c).mpr hcop
  have hmem := (weightedG2_mem_g2Span_iff _).mpr
    (weightedG2MF_mem_primitiveG2Subspace_of_support hsupp)
  have hlift : weightedG2 Wπ = weightedG2 W := weightedG2_comp_castHom h W
  rwa [← weightedG2ₗ_apply, map_sub, weightedG2ₗ_apply, weightedG2ₗ_apply, hWp, hlift] at hmem

/-- **Raising the level by a prime.** For a prime `p` and `N = M p`, the series of a weight modulo
`M` supported on the residues of coprime pairs is the series of a primitive weight modulo `N`. If
`p ∣ M` the residues `p e` carry no weight. Otherwise multiplication by `p` permutes the residues
modulo `M`, and iterating `weightedG2_sub_mem_g2Span` along its orbit shows that
`(1 - p^{-2r}) G₂^W` is primitive modulo `N`, for the order `r` of `p` modulo `M`. -/
private lemma weightedG2_mem_g2Span_of_eq_mul_prime {p : ℕ} (hp : p.Prime) (hNM : N = M * p)
    {W : (Fin 2 → ZMod M) → ℂ} (hW : ∀ e, W e ≠ 0 → Nonempty (gammaSet M 1 e)) :
    weightedG2 W ∈ g2Span N := by
  by_cases hpM : p ∣ M
  · have h0 : (fun e ↦ W ((p : ZMod M) • e)) = 0 := funext fun e ↦ by_contra fun hne ↦ by
      have hcop := (nonempty_gammaSet_natCast_smul_iff p e).mp (hW _ hne)
      exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_mul_right hcop) hpM)
    simpa [h0, weightedG2_zero] using weightedG2_sub_mem_g2Span hp hNM hW
  have hcop : Nat.Coprime p M := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpM
  let u : (ZMod M)ˣ := ZMod.unitOfCoprime p hcop
  -- the weights `e ↦ W (p ^ j e)`
  let V (j : ℕ) : (Fin 2 → ZMod M) → ℂ := fun e ↦ W ((u ^ j : (ZMod M)ˣ) • e)
  have hV (j : ℕ) (e : Fin 2 → ZMod M) (he : V j e ≠ 0) : Nonempty (gammaSet M 1 e) := by
    have hcop' := (nonempty_gammaSet_natCast_smul_iff (p ^ j) e).mp (by
      simpa [u, Units.smul_def] using hW _ he)
    exact (nonempty_gammaSet_iff_coprime_val e).mpr (Nat.Coprime.coprime_mul_left hcop')
  have hVsucc (j : ℕ) : (fun e ↦ V j ((p : ZMod M) • e)) = V (j + 1) := by
    ext e
    simp [V, u, Units.smul_def, smul_smul, pow_succ]
  -- iterate along the orbit of multiplication by `p`
  have hiter (j : ℕ) :
      weightedG2 W - (((p : ℂ) ^ 2)⁻¹) ^ j • weightedG2 (V j) ∈ g2Span N := by
    induction j with
    | zero => simp [V, sub_self]
    | succ j ih =>
      have hR := weightedG2_sub_mem_g2Span hp hNM (hV j)
      rw [hVsucc] at hR
      convert (g2Span N).add_mem ih ((g2Span N).smul_mem ((((p : ℂ) ^ 2)⁻¹) ^ j) hR) using 1
      rw [smul_sub, smul_smul, ← pow_succ]
      abel
  have hr := orderOf_pos u
  have hVr : V (orderOf u) = W := by
    ext e
    simp [V, pow_orderOf_eq_one]
  have h := hiter (orderOf u)
  rw [hVr, ← one_smul ℂ (weightedG2 W), smul_smul, mul_one, ← sub_smul] at h
  refine ((g2Span N).smul_mem_iff (sub_ne_zero.mpr fun h1 ↦ ?_)).mp h
  rw [inv_pow] at h1
  have h1' : ((p ^ (2 * orderOf u) : ℕ) : ℂ) = 1 := by
    rw [pow_mul, Nat.cast_pow, Nat.cast_pow]
    exact inv_eq_one.mp h1.symm
  exact hp.one_lt.ne' ((Nat.pow_eq_one.mp (by exact_mod_cast h1')).resolve_right (by omega))

/-- **Raising the level.** For `M ∣ N`, the series of a weight modulo `M` supported on the residues
of coprime pairs is the series of a primitive weight modulo `N`, by raising the level one prime at
a time. -/
private lemma weightedG2_mem_g2Span_of_dvd (h : M ∣ N) {W : (Fin 2 → ZMod M) → ℂ}
    (hW : ∀ e, W e ≠ 0 → Nonempty (gammaSet M 1 e)) : weightedG2 W ∈ g2Span N := by
  induction hk : N / M using Nat.strong_induction_on generalizing M with
  | _ k ih =>
    by_cases hk1 : k = 1
    · obtain rfl : M = N := Nat.eq_of_dvd_of_div_eq_one h (hk.trans hk1)
      exact (weightedG2_mem_g2Span_iff W).mpr
        (weightedG2MF_mem_primitiveG2Subspace_of_support hW)
    have hk0 : k ≠ 0 := by
      rw [← hk]
      exact (Nat.div_pos (Nat.le_of_dvd (NeZero.pos N) h) (NeZero.pos M)).ne'
    have hp := Nat.minFac_prime hk1
    have : NeZero (M * k.minFac) := ⟨mul_ne_zero (NeZero.ne M) hp.ne_zero⟩
    have hdvd : M * k.minFac ∣ N := by
      obtain ⟨n, hn⟩ := h
      subst hn
      rw [Nat.mul_div_cancel_left _ (NeZero.pos M)] at hk
      exact Nat.mul_dvd_mul_left M (hk ▸ Nat.minFac_dvd k)
    obtain ⟨W', hW', hWW'⟩ := weightedG2_mem_g2Span_of_eq_mul_prime hp rfl hW
    rw [← hWW', weightedG2ₗ_apply]
    refine ih (k / k.minFac) (Nat.div_lt_self (Nat.pos_of_ne_zero hk0) hp.one_lt) hdvd
      (mem_primitiveG2Weights_iff.mp hW').1 ?_
    rw [← Nat.div_div_eq_div_mul, hk]

/-- **Every weighted weight-two series lies in the primitive weight-two Eisenstein subspace.**
Writing a residue pair `a` modulo `N` as `g e` with `g = gcd(a₀, a₁, N)`, the series of the single
residue `a` is `g⁻²` times that of `e` at level `N / g`, and `e` is the residue of a coprime pair;
its series is the series of a primitive weight at level `N`. -/
theorem weightedG2MF_mem_primitiveG2Subspace (W : (Fin 2 → ZMod N) → ℂ) :
    weightedG2MF W ∈ primitiveG2Subspace N := by
  classical
  rw [← weightedG2_mem_g2Span_iff, weightedG2_eq_sum_single]
  refine Submodule.sum_mem _ fun a _ ↦ Submodule.smul_mem _ _ ?_
  set g := ((a 0).val.gcd (a 1).val).gcd N
  have hgN : g ∣ N := Nat.gcd_dvd_right _ _
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_right _ (NeZero.pos N)
  have : NeZero (N / g) := ⟨(Nat.div_pos (Nat.le_of_dvd (NeZero.pos N) hgN) hg0).ne'⟩
  have hdvd (i : Fin 2) : g ∣ (a i).val := (Nat.gcd_dvd_left _ _).trans (by
    fin_cases i
    exacts [Nat.gcd_dvd_left _ _, Nat.gcd_dvd_right _ _])
  -- the residue `e = a / g` modulo `N / g`
  let e : Fin 2 → ZMod (N / g) := fun i ↦ (((a i).val / g : ℕ) : ZMod (N / g))
  have hval (i : Fin 2) : (e i).val = (a i).val / g :=
    ZMod.val_natCast_of_lt (Nat.div_lt_div_of_lt_of_dvd hgN (a i).val_lt)
  rw [weightedG2_single_eq_of_val_eq (Nat.mul_div_cancel' hgN).symm fun i ↦ by
    rw [hval, Nat.mul_div_cancel' (hdvd i)]]
  refine Submodule.smul_mem _ _ ?_
  have he : Nonempty (gammaSet (N / g) 1 e) := by
    rw [nonempty_gammaSet_iff_coprime_val, hval, hval, Nat.gcd_div (hdvd 0) (hdvd 1)]
    exact Nat.coprime_div_gcd_div_gcd hg0
  refine weightedG2_mem_g2Span_of_dvd (Nat.div_dvd_of_dvd hgN) fun b hb ↦ ?_
  by_contra hne
  exact hb (Pi.single_eq_of_ne (fun hbe : b = e ↦ hne (by rw [hbe]; exact he)) _)

/-- The primitive weight-two Eisenstein subspace of `M₂(Γ(N))` is spanned by all the weighted
series `G₂^W`. -/
theorem range_weightedG2MFₗ :
    LinearMap.range (weightedG2MFₗ (N := N)) = primitiveG2Subspace N := by
  refine le_antisymm ?_ fun f hf ↦ ?_
  · rintro _ ⟨W, rfl⟩
    rw [weightedG2MFₗ_apply]
    exact weightedG2MF_mem_primitiveG2Subspace W
  · obtain ⟨W, -, rfl⟩ := mem_primitiveG2Subspace_iff.mp hf
    exact ⟨W, weightedG2MFₗ_apply W⟩

end TauCeti.EisensteinSeries
