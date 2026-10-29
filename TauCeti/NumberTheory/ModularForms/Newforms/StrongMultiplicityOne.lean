/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Newforms.EigenvectorVanishing
public import TauCeti.NumberTheory.ModularForms.Newforms.EigenvalueExtension
public import TauCeti.NumberTheory.ModularForms.Newforms.Coefficient
public import TauCeti.NumberTheory.ModularForms.Newforms.OldAtPrime
public import TauCeti.NumberTheory.ModularForms.Newforms.PrimeDecomposition

/-!
# Strong multiplicity one

Two newforms of level `N`, weight `k` and the same nebentypus whose eigenvalues agree at every
index coprime to `N` outside a finite set are equal (Miyake, Theorem 4.6.12). The finite slack is
what makes the statement *strong*: nothing at all is assumed at the indices dividing the level.

The same argument, run on `f - a₁(g)⁻¹ V₁ g` (the level-raise of `g` renormalised to `a₁ = 1`)
instead of `f - g`, rigidifies the level across divisors: a
good Hecke eigenform `g` of a level `M ∣ N` with `a₁(g) ≠ 0` whose nebentypus induces that of a
newform `f` of level `N`, and whose eigenvalues agree with those of `f` at every prime `p ∤ N`,
has `M = N` (`Newform.level_eq_of_dvd_of_forall_prime_eigenvalue_eq`). This is the divisor-level
case of strong multiplicity one across levels (Miyake, Theorem 4.6.19), with agreement asked at
every good prime rather than outside a finite set.

The agreement extends from the complement of the finite set to every good index
(`EigenformAwayFromLevel.eigenvalue_eq_of_forall_notMem`), so the difference of the two underlying
cusp forms is a good Hecke eigenvector with `a₁ = 0`; its coefficients therefore vanish at every
index coprime to `N`, so it is old by the Main Lemma
(`TauCeti.mem_cuspFormsOld_of_forall_coprime_qExpansion_coeff_eq_zero`). Being a difference of
newforms it is also new, and old and new are disjoint, so it is zero.

Miyake states the theorem on the Fourier coefficients rather than the eigenvalues; for a
normalised newform the coefficient at a good index *is* the eigenvalue there
(`EigenformAwayFromLevel.qExpansion_coeff_eq_eigenvalue` with `Newform.isNorm`), so that form is
a corollary.

Across unrelated levels, two newforms `f`, `g` of levels `N`, `M` whose nebentypes induce the
same character modulo `lcm N M` and whose eigenvalues agree at all but finitely many primes
`p ∤ N M` have `N = M` (`Newform.level_eq_of_forall_notMem_prime_eigenvalue_eq`). Nothing is
assumed at the primes dividing `N M`; the two forms are separated by the `q`-new subspaces
(`TauCeti.cuspFormsNewAt`) at a prime `q` where the levels have different valuations.

## Main results

* `HeckeRing.GL2.Newform.eq_of_forall_prime_eigenvalue_eq`: a newform is determined by its
  eigenvalues at the primes not dividing the level.
* `HeckeRing.GL2.Newform.eq_of_forall_notMem_eigenvalue_eq`: strong multiplicity one, on the
  eigenvalues.
* `HeckeRing.GL2.Newform.eq_of_forall_notMem_qExpansion_coeff_eq`: Miyake's own form, on the
  `q`-expansion coefficients.
* `HeckeRing.GL2.Newform.level_eq_of_dvd_of_forall_prime_eigenvalue_eq`: a good Hecke eigenform
  of a divisor level `M ∣ N` with `a₁ ≠ 0` sharing the nebentypus and the good eigensystem of a
  newform of level `N` has `M = N`.
* `HeckeRing.GL2.Newform.level_eq_of_forall_notMem_prime_eigenvalue_eq`: two newforms of levels
  `N` and `M` with compatible nebentypes whose eigenvalues agree at all but finitely many primes
  `p ∤ N M` have `N = M` (Miyake, Theorem 4.6.19, for newforms).

## Provenance

Adapted from the AINTLIB `LeanModularForms` project (Chris Birkbeck, Apache-2.0,
<https://github.com/CBirkbeck/AINTLIB> @ `2baa76f742bd`),
`projects/LeanModularForms/LeanModularForms/StrongMultiplicityOne/ConstantMultiple.lean` —
declaration `strongMultiplicityOne`. The source routes through
`strongMultiplicityOne_constMul` (a newform and an eigenform sharing eigenvalues are
proportional, with `a₁ = 1` pinning the constant); here the difference is shown to be zero
directly from the Main Lemma and the disjointness of the old and new subspaces, so the
proportionality step is not needed. The comparison across unrelated levels is not taken from
there; it follows the `q`-new decomposition of Atkin–Lehner and Li.

## References

* [T. Miyake, *Modular forms*][miyake1989], Theorem 4.6.12, and Theorem 4.6.19 for the
  cross-level statement.
* W.-C. W. Li, *Newforms and functional equations*, Math. Ann. 212 (1975), 285–315, for the
  comparison across levels through the `q`-new subspaces.
* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005],
  Theorem 5.8.2 (the `∀ n` coprime version; the strong form is deferred to Miyake).
-/

public section

open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup TauCeti

open scoped MatrixGroups

namespace HeckeRing.GL2

variable {N : ℕ} [NeZero N] {k : ℤ}

/-- **The difference of two eigenvectors of the classical `T_p` with a common eigenvalue is a
ring eigenvector there**, on `S_k(N, χ)`: at a prime the ring generator acts as the classical
operator, which scales `F` and `G`, hence `F - G`, by the common value. -/
private theorem exists_heckeRingHomCuspCharSpace_sub_eq_smul {χ : (ZMod N)ˣ →* ℂˣ} {p : ℕ}
    (hp : p.Prime) {F G : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} {c : ℂ}
    (hF : heckeTCuspNat k p (_hn := ⟨hp.ne_zero⟩) F = c • F)
    (hG : heckeTCuspNat k p (_hn := ⟨hp.ne_zero⟩) G = c • G)
    {d : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hd : d = F - G) (hdχ : d ∈ cuspFormCharSpace k χ) :
    ∃ c : ℂ, heckeRingHomCuspCharSpace k χ (heckeTCompositeGamma0 N p) ⟨d, hdχ⟩ = c • ⟨d, hdχ⟩ :=
  have : NeZero p := ⟨hp.ne_zero⟩
  ⟨c, heckeRingHomCuspCharSpace_heckeTCompositeGamma0_eq_smul_of_heckeTCuspNat_eq_smul hp <| by
    simp only [hd, map_sub, hF, hG, smul_sub]⟩

/-- **A newform is determined by its eigenvalues at the good primes**: two newforms of level
`N`, weight `k` and the same nebentypus with the same eigenvalue at every prime not dividing `N`
are equal. -/
theorem Newform.eq_of_forall_prime_eigenvalue_eq {f g : Newform N k} (hχ : f.χ = g.χ)
    (h : ∀ (p : ℕ) (hp : p.Prime) (hpN : Nat.Coprime p N),
      f.eigenvalue ⟨p, hp.pos⟩ hpN = g.eigenvalue ⟨p, hp.pos⟩ hpN) :
    f = g := by
  -- the difference is a good Hecke eigenvector with `a₁ = 0`
  set d : CuspForm ((Gamma1 N).map (mapGL ℝ)) k := f.toCuspForm - g.toCuspForm with hd
  have hdχ : d ∈ cuspFormCharSpace k f.χ :=
    Submodule.sub_mem _ f.mem_charSpace (hχ ▸ g.mem_charSpace)
  have heig := fun (p : ℕ) (hp : p.Prime) (hpN : Nat.Coprime p N) ↦
    exists_heckeRingHomCuspCharSpace_sub_eq_smul hp (f.heckeTCuspNat_eq_eigenvalue_smul hp hpN)
      (by rw [g.heckeTCuspNat_eq_eigenvalue_smul hp hpN, h p hp hpN]) hd hdχ
  have h1 : (qExpansion 1 d).coeff 1 = 0 := by
    rw [hd, FunLike.coe_sub,
      ModularForm.qExpansion_sub one_pos (one_mem_strictPeriods_Gamma1_map _), map_sub, f.isNorm,
      g.isNorm, sub_self]
  -- so its coefficients vanish off `N`, and it is old; it is also new, hence zero
  have hd0 : d = 0 :=
    eq_zero_of_forall_prime_heckeRingHomCusp_of_one_eq_zero_of_mem_cuspFormsNew
      (F := ⟨d, hdχ⟩) heig h1 (Submodule.sub_mem _ f.isNew g.isNew)
  exact Newform.ext (sub_eq_zero.mp hd0)

/-- **Strong multiplicity one** (Miyake, Theorem 4.6.12, fixed level and nebentypus): two
newforms of level `N`, weight `k` and the same nebentypus whose eigenvalues agree at every index
coprime to `N` outside a finite set are equal. -/
theorem Newform.eq_of_forall_notMem_eigenvalue_eq {f g : Newform N k} (hχ : f.χ = g.χ)
    {S : Finset ℕ}
    (h : ∀ (n : ℕ+) (hn : Nat.Coprime n N), (n : ℕ) ∉ S → f.eigenvalue n hn = g.eigenvalue n hn) :
    f = g :=
  Newform.eq_of_forall_prime_eigenvalue_eq hχ fun p hp hpN ↦
    EigenformAwayFromLevel.eigenvalue_eq_of_forall_notMem h (p := ⟨p, hp.pos⟩) hpN

/-- **Strong multiplicity one, on Fourier coefficients** (Miyake's own form of Theorem 4.6.12):
two newforms of level `N`, weight `k` and the same nebentypus whose `q`-expansion coefficients
agree at every index coprime to `N` outside a finite set are equal. For a normalised newform the
coefficient at a good index *is* the eigenvalue there
(`HeckeRing.GL2.EigenformAwayFromLevel.qExpansion_coeff_eq_eigenvalue`), so this is the eigenvalue
form. -/
theorem Newform.eq_of_forall_notMem_qExpansion_coeff_eq {f g : Newform N k} (hχ : f.χ = g.χ)
    {S : Finset ℕ}
    (h : ∀ (n : ℕ+), Nat.Coprime (n : ℕ) N → (n : ℕ) ∉ S →
      (qExpansion 1 f.toCuspForm).coeff (n : ℕ) = (qExpansion 1 g.toCuspForm).coeff (n : ℕ)) :
    f = g :=
  Newform.eq_of_forall_notMem_eigenvalue_eq hχ fun n hn hnS ↦ by
    rw [← f.toEigenformAwayFromLevel.qExpansion_coeff_eq_eigenvalue f.isNorm n hn,
      ← g.toEigenformAwayFromLevel.qExpansion_coeff_eq_eigenvalue g.isNorm n hn]
    exact h n hn hnS

/-! ### Across divisor levels -/

/-- **A good Hecke eigenform of a divisor level with `a₁ ≠ 0` that shares the nebentypus and
the good eigensystem of a newform of level `N` has level `N`.** If `g` is a good Hecke eigenform
of level `M ∣ N` with `a₁(g) ≠ 0` whose nebentypus induces that of the newform `f` of level `N`,
and whose eigenvalue agrees with that of `f` at every prime not dividing `N`, then `M = N`.
Nothing requires `g` to be new; for a newform `g` the hypothesis on `a₁` is `Newform.isNorm`.

Compare Miyake, Theorem 4.6.19 (strong multiplicity one across levels, for newforms): this is
its divisor-level case, with agreement asked at every good prime rather than outside a finite
set. -/
theorem Newform.level_eq_of_dvd_of_forall_prime_eigenvalue_eq {M : ℕ} [NeZero M]
    (f : Newform N k) (g : EigenformAwayFromLevel M k)
    (hg₁ : (qExpansion 1 g.toCuspForm).coeff 1 ≠ 0) (hMN : M ∣ N)
    (hχ : g.χ.comp (ZMod.unitsMap hMN) = f.χ)
    (h : ∀ (p : ℕ) (hp : p.Prime) (hpN : Nat.Coprime p N),
      g.eigenvalue ⟨p, hp.pos⟩ (hpN.coprime_dvd_right hMN) = f.eigenvalue ⟨p, hp.pos⟩ hpN) :
    M = N := by
  by_contra hne
  have h1 : 1 * M ∣ N := by rwa [one_mul]
  -- `V₁ g` at level `N`, rescaled to `a₁ = 1`: old, of nebentypus `χ`, and a good eigenvector
  -- with the eigenvalues of `f`
  set G : CuspForm ((Gamma1 N).map (mapGL ℝ)) k := ((qExpansion 1 g.toCuspForm).coeff 1)⁻¹ •
    CuspForm.levelRaise 1 (Gamma1_map_le_conjAct_scaleGL_of_dvd h1) g.toCuspForm with hG
  have hGold : G ∈ cuspFormsOld N k :=
    Submodule.smul_mem _ _ (levelRaise_mem_cuspFormsOld h1 hne k g.toCuspForm)
  have hGχ : G ∈ cuspFormCharSpace k f.χ := by
    have := CuspForm.levelRaise_mem_cuspFormCharSpace_of_dvd h1 g.χ g.mem_charSpace
    rw [hχ] at this
    exact Submodule.smul_mem _ _ this
  have hG1 : (qExpansion 1 G).coeff 1 = 1 := by
    rw [hG, FunLike.coe_smul,
      ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods_Gamma1_map _),
      PowerSeries.coeff_smul, CuspForm.qExpansion_levelRaise_coeff
        (one_mem_strictPeriods_Gamma1_map _) (one_mem_strictPeriods_Gamma1_map _)]
    simp [inv_mul_cancel₀ hg₁]
  have hGeig : ∀ (p : ℕ) (hp : p.Prime) (hpN : Nat.Coprime p N),
      heckeTCuspNat k p (_hn := ⟨hp.ne_zero⟩) G = f.eigenvalue ⟨p, hp.pos⟩ hpN • G := by
    intro p hp hpN
    have : NeZero p := ⟨hp.ne_zero⟩
    rw [hG, map_smul, g.heckeTCuspNat_levelRaise_eq_eigenvalue_smul h1 hp hpN, h p hp hpN,
      smul_comm]
  -- the difference `f - G` is a good Hecke eigenvector of `S_k(N, χ)` with `a₁ = 0`
  set d : CuspForm ((Gamma1 N).map (mapGL ℝ)) k := f.toCuspForm - G with hd
  have hdχ : d ∈ cuspFormCharSpace k f.χ := Submodule.sub_mem _ f.mem_charSpace hGχ
  have hdeig := fun (p : ℕ) (hp : p.Prime) (hpN : Nat.Coprime p N) ↦
    exists_heckeRingHomCuspCharSpace_sub_eq_smul hp (f.heckeTCuspNat_eq_eigenvalue_smul hp hpN)
      (hGeig p hp hpN) hd hdχ
  have hd1 : (qExpansion 1 d).coeff 1 = 0 := by
    rw [hd, FunLike.coe_sub,
      ModularForm.qExpansion_sub one_pos (one_mem_strictPeriods_Gamma1_map _), map_sub, f.isNorm,
      hG1, sub_self]
  -- so it is old, and then so is `f = (f - G) + G`; but `f` is new and nonzero
  have hdold : d ∈ cuspFormsOld N k :=
    mem_cuspFormsOld_of_forall_prime_heckeRingHomCusp_of_one_eq_zero hdeig hd1
  have hfold : f.toCuspForm ∈ cuspFormsOld N k := by
    have := Submodule.add_mem _ hdold hGold
    rwa [hd, sub_add_cancel] at this
  exact f.ne_zero
    ((Submodule.disjoint_def.mp (disjoint_cuspFormsOld_cuspFormsNew N k)) _ hfold f.isNew)

/-! ### Across unrelated levels -/

/-- **The `q`-new part of `V_p F` has vanishing first coefficient**, for primes `p ∣ L` and `q`,
and `F` of level `L / p`. -/
private theorem qExpansion_coeff_one_projection_levelRaise_eq_zero {L p q : ℕ} [NeZero L]
    [NeZero p] (hp : p.Prime) (hq : q.Prime) (hpL : p ∣ L)
    (F : CuspForm ((Gamma1 (L / p)).map (mapGL ℝ)) k) :
    (qExpansion 1 ((cuspFormsNewAt L k q).projection (cuspFormsOldAt L k q)
      (isCompl_cuspFormsOldAt_cuspFormsNewAt L k q).symm
        (CuspForm.levelRaise p (Gamma1_map_le_conjAct_scaleGL_of_dvd
          (Nat.mul_div_cancel' hpL).dvd) F))).coeff 1 = 0 := by
  -- if `p = q`, then `V_q F` is `q`-old. Otherwise split `F` along the `q`-old and `q`-new
  -- subspaces of level `L / p`: `V_p` keeps the first part `q`-old and the second `q`-new, as
  -- `q (L / p) ∤ L`, so the `q`-new part of `V_p F` is a level-raise by `p ≠ 1`, whose
  -- coefficients sit at the multiples of `p`
  have : NeZero (L / p) := ⟨(Nat.div_pos (Nat.le_of_dvd (NeZero.pos L) hpL) hp.pos).ne'⟩
  have hpLp : p * (L / p) ∣ L := (Nat.mul_div_cancel' hpL).dvd
  by_cases hpq : p = q
  · subst hpq
    rw [Submodule.projection_apply_of_mem_right _
      (levelRaise_mem_cuspFormsOldAt hpLp hpLp k _), FunLike.coe_zero,
      qExpansion_zero, map_zero]
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp
    ((isCompl_cuspFormsOldAt_cuspFormsNewAt (L / p) k q).sup_eq_top ▸ Submodule.mem_top (x := F))
  have hqLp : ¬q * (L / p) ∣ L := fun h ↦ hpq <| ((Nat.prime_dvd_prime_iff_eq hq hp).mp
    (Nat.dvd_of_mul_dvd_mul_right (Nat.pos_of_ne_zero (NeZero.ne (L / p)))
      (by rwa [Nat.mul_div_cancel' hpL]))).symm
  rw [← CuspForm.levelRaiseₗ_apply, map_add, CuspForm.levelRaiseₗ_apply,
    CuspForm.levelRaiseₗ_apply, map_add, Submodule.projection_apply_of_mem_right _
      (levelRaise_mem_cuspFormsOldAt_of_mem hpLp ha),
    Submodule.projection_apply_of_mem_left _ (levelRaise_mem_cuspFormsNewAt hq hpLp hqLp hb),
    zero_add, CuspForm.qExpansion_levelRaise_coeff (one_mem_strictPeriods_Gamma1_map _)
      (one_mem_strictPeriods_Gamma1_map _),
    ite_eq_right_iff.mpr fun h ↦ absurd (Nat.dvd_one.mp h) hp.ne_one]

/-- **Newforms are separated at a level telling their `q`-parts apart.** Let `f`, `g` be
newforms of levels `N`, `M`, and `L` a common multiple, for a prime `q` with `q N ∣ L` and
`q M ∤ L`. Their nebentypes cannot agree at level `L` while their eigenvalues agree at every prime
`p ∤ L`. -/
private theorem false_of_mul_dvd_of_not_mul_dvd {M L q : ℕ} [NeZero M] [NeZero L]
    (f : Newform N k) (g : Newform M k) (hq : q.Prime) (hqN : q * N ∣ L)
    (hML : M ∣ L) (hqML : ¬q * M ∣ L)
    (hχ : f.χ.comp (ZMod.unitsMap (dvd_of_mul_left_dvd hqN)) = g.χ.comp (ZMod.unitsMap hML))
    (h : ∀ (p : ℕ) (hp : p.Prime) (hpL : p.Coprime L),
      f.eigenvalue ⟨p, hp.pos⟩ (hpL.coprime_dvd_right (dvd_of_mul_left_dvd hqN)) =
        g.eigenvalue ⟨p, hp.pos⟩ (hpL.coprime_dvd_right hML)) :
    False := by
  -- `V₁ f − V₁ g` at level `L` is a sum of `V_p F_p` over the primes `p ∣ L`. Project onto the
  -- `q`-new subspace along the `q`-old one and read off `a₁`: `V₁ f` is `q`-old and `V₁ g` is
  -- `q`-new, while the projection of every `V_p F_p` has `a₁ = 0`. So `0 - 1 = 0`.
  have : NeZero q := ⟨hq.ne_zero⟩
  have h1N : 1 * N ∣ L := by rw [one_mul]; exact dvd_of_mul_left_dvd hqN
  have h1M : 1 * M ∣ L := by rwa [one_mul]
  -- the first `q`-expansion coefficient at level `L`
  set ℓ := CuspForm.qExpansionCoeffₗ one_pos (one_mem_strictPeriods_Gamma1_map L) k 1
  -- `V₁ f − V₁ g` is a good Hecke eigenvector of `S_k(L, χ)` with `a₁ = 0`
  set F := CuspForm.levelRaise 1 (Gamma1_map_le_conjAct_scaleGL_of_dvd h1N) f.toCuspForm
  set G := CuspForm.levelRaise 1 (Gamma1_map_le_conjAct_scaleGL_of_dvd h1M) g.toCuspForm
  set χ := f.χ.comp (ZMod.unitsMap (dvd_of_mul_left_dvd hqN))
  have hFχ : F ∈ cuspFormCharSpace k χ :=
    CuspForm.levelRaise_mem_cuspFormCharSpace_of_dvd h1N f.χ f.mem_charSpace
  have hGχ : G ∈ cuspFormCharSpace k χ := by
    rw [hχ]
    exact CuspForm.levelRaise_mem_cuspFormCharSpace_of_dvd h1M g.χ g.mem_charSpace
  set D := F - G with hD
  have hDχ : D ∈ cuspFormCharSpace k χ := Submodule.sub_mem _ hFχ hGχ
  have heig : ∀ p : ℕ, p.Prime → Nat.Coprime p L → ∃ c : ℂ,
      heckeRingHomCuspCharSpace k χ (heckeTCompositeGamma0 L p) ⟨D, hDχ⟩ = c • ⟨D, hDχ⟩ :=
    fun p hp hpL ↦ exists_heckeRingHomCuspCharSpace_sub_eq_smul hp
      (f.heckeTCuspNat_levelRaise_eq_eigenvalue_smul h1N hp hpL)
      (by rw [g.heckeTCuspNat_levelRaise_eq_eigenvalue_smul h1M hp hpL, ← h p hp hpL]) hD hDχ
  have hcoeff : ∀ {X : ℕ} (hX : 1 * X ∣ L) (x : CuspForm ((Gamma1 X).map (mapGL ℝ)) k),
      ℓ (CuspForm.levelRaise 1 (Gamma1_map_le_conjAct_scaleGL_of_dvd hX) x) =
        (qExpansion 1 x).coeff 1 := fun _ _ ↦ by
    simp [ℓ]
  have h1 : ℓ D = 0 := by
    rw [hD, map_sub, hcoeff h1N, hcoeff h1M, f.isNorm, g.isNorm, sub_self]
  -- so `D` is a sum of `V_p F_p` over the primes `p ∣ L`
  obtain ⟨Fp, hsum⟩ := exists_eq_sum_levelRaise_prime_of_forall_coprime_qExpansion_coeff_eq_zero
    hDχ fun n hn ↦
      qExpansion_coeff_eq_zero_of_forall_prime_heckeRingHomCusp_of_one_eq_zero_of_coprime
        (F := ⟨D, hDχ⟩) dvd_rfl heig (by rwa [CuspForm.qExpansionCoeffₗ_apply] at h1) n hn
  -- project onto the `q`-new subspace and read off `a₁`
  set P := (cuspFormsNewAt L k q).projection (cuspFormsOldAt L k q)
    (isCompl_cuspFormsOldAt_cuspFormsNewAt L k q).symm
  have hF : P F = 0 := Submodule.projection_apply_of_mem_right _
    (levelRaise_mem_cuspFormsOldAt h1N hqN k _)
  have hG : P G = G := Submodule.projection_apply_of_mem_left _ <|
    levelRaise_mem_cuspFormsNewAt hq h1M hqML
      (cuspFormsNew_le_cuspFormsNewAt hq.ne_one g.isNew)
  have hp : ∀ p : {p // p ∈ L.primeFactors},
      haveI : NeZero p.1 := ⟨(Nat.prime_of_mem_primeFactors p.2).ne_zero⟩
      ℓ (P (CuspForm.levelRaise p.1 (Gamma1_map_le_conjAct_scaleGL_of_dvd
        (Nat.mul_div_cancel' (Nat.dvd_of_mem_primeFactors p.2)).dvd) (Fp p))) = 0 := fun p ↦
    have : NeZero p.1 := ⟨(Nat.prime_of_mem_primeFactors p.2).ne_zero⟩
    (CuspForm.qExpansionCoeffₗ_apply _ _ _ _).trans
      (qExpansion_coeff_one_projection_levelRaise_eq_zero (Nat.prime_of_mem_primeFactors p.2) hq
        (Nat.dvd_of_mem_primeFactors p.2) _)
  have hℓG : ℓ G = 1 := (hcoeff h1M _).trans g.isNorm
  have key := congrArg (fun x ↦ ℓ (P x)) hsum
  simp only [hD, map_sub, hF, hG, map_sum, hp, Finset.sum_const_zero, zero_sub, map_neg, hℓG,
    neg_eq_zero] at key
  exact one_ne_zero key

/-- **Strong multiplicity one across levels, the level half, when `M ∤ N`**: two newforms of
levels `N`, `M` with `M ∤ N` cannot have compatible nebentypes and eigenvalues agreeing at all
but finitely many primes `p ∤ N M`. -/
private theorem false_of_not_dvd {M : ℕ} [NeZero M] (f : Newform N k) (g : Newform M k)
    (hχ : f.χ.comp (ZMod.unitsMap (Nat.dvd_lcm_left N M)) =
      g.χ.comp (ZMod.unitsMap (Nat.dvd_lcm_right N M))) {S : Finset ℕ}
    (h : ∀ (p : ℕ) (hp : p.Prime) (hpN : p.Coprime N) (hpM : p.Coprime M), p ∉ S →
      f.eigenvalue ⟨p, hp.pos⟩ hpN = g.eigenvalue ⟨p, hp.pos⟩ hpM)
    (hMN : ¬M ∣ N) : False := by
  -- choose a prime `q` with `v_q(N) < v_q(M)` and compare at `L = lcm N M · ∏ p`, the product
  -- over the exceptional primes prime to `N M`: its `q`-part is that of `M`, and every prime not
  -- dividing it is good for both forms and outside `S`
  have hN0 := NeZero.ne N
  have hM0 := NeZero.ne M
  -- a prime at which `M` has the larger valuation
  obtain ⟨q, hqNM⟩ : ∃ q, N.factorization q < M.factorization q := by
    by_contra! H
    exact hMN ((Nat.factorization_le_iff_dvd hM0 hN0).mp fun q ↦ H q)
  have hqM' : q ∈ M.primeFactors := Nat.support_factorization M ▸
    Finsupp.mem_support_iff.mpr (by omega)
  have hq := Nat.prime_of_mem_primeFactors hqM'
  have hqM := Nat.dvd_of_mem_primeFactors hqM'
  -- the working level
  set P := ∏ p ∈ S.filter (fun p ↦ p.Prime ∧ p.Coprime (N * M)), p with hP
  have hP0 : P ≠ 0 := Finset.prod_ne_zero_iff.mpr fun p hp ↦
    (Finset.mem_filter.mp hp).2.1.ne_zero
  have hqP : ¬q ∣ P := fun hqP ↦ by
    obtain ⟨p, hp, hqp⟩ := (Prime.dvd_finsetProd_iff hq.prime _).mp hqP
    obtain ⟨-, hp, hpNM⟩ := Finset.mem_filter.mp hp
    rw [← (Nat.prime_dvd_prime_iff_eq hq hp).mp hqp] at hpNM
    exact hq.ne_one (Nat.Coprime.eq_one_of_dvd hpNM (dvd_mul_of_dvd_right hqM N))
  have hlcm0 : Nat.lcm N M ≠ 0 := Nat.lcm_ne_zero hN0 hM0
  set L := Nat.lcm N M * P
  have : NeZero L := ⟨mul_ne_zero hlcm0 hP0⟩
  have hqN : q * N ∣ L := by
    refine Dvd.dvd.mul_right ((Nat.factorization_le_iff_dvd (mul_ne_zero hq.ne_zero hN0)
      hlcm0).mp fun p ↦ ?_) P
    rw [Nat.factorization_mul hq.ne_zero hN0, Nat.factorization_lcm hN0 hM0, hq.factorization]
    simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply, Finsupp.sup_apply]
    split_ifs with hqp
    · subst hqp; omega
    · omega
  have hqML : ¬q * M ∣ L := fun hdvd ↦ by
    have := (Nat.factorization_le_iff_dvd (mul_ne_zero hq.ne_zero hM0)
      (mul_ne_zero hlcm0 hP0)).mpr hdvd q
    rw [Nat.factorization_mul hq.ne_zero hM0, Nat.factorization_mul hlcm0 hP0,
      Nat.factorization_lcm hN0 hM0, hq.factorization] at this
    simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same, Finsupp.sup_apply,
      Nat.factorization_eq_zero_of_not_dvd hqP] at this
    omega
  have hML : M ∣ L := (Nat.dvd_lcm_right N M).mul_right P
  refine false_of_mul_dvd_of_not_mul_dvd f g hq hqN hML hqML ?_ fun p hp hpL ↦ ?_
  · rw [← ZMod.unitsMap_comp (Nat.dvd_lcm_left N M) (dvd_mul_right _ P), ← MonoidHom.comp_assoc,
      hχ, MonoidHom.comp_assoc, ZMod.unitsMap_comp]
  · have hpNM : p.Coprime (N * M) := Nat.Coprime.mul_right
      (hpL.coprime_dvd_right ((Nat.dvd_lcm_left N M).mul_right P))
      (hpL.coprime_dvd_right hML)
    refine h p hp _ _ fun hpS ↦ hp.ne_one (Nat.Coprime.eq_one_of_dvd hpL ?_)
    exact (Finset.dvd_prod_of_mem _ (Finset.mem_filter.mpr ⟨hpS, hp, hpNM⟩)).mul_left _

/-- **Strong multiplicity one across levels, the level** (Miyake, Theorem 4.6.19, for
newforms). Let `f`, `g` be newforms of the same weight and of levels `N`, `M` whose nebentypes
induce the same character modulo `lcm N M`, and whose eigenvalues agree at every prime
`p ∤ N M` outside a finite set `S`. Then `N = M`.

Nothing is assumed at the primes dividing `N M`, nor at the finitely many primes of `S`. With
`N = M` in hand, `Newform.eq_of_forall_prime_eigenvalue_eq` gives `f = g` when the eigenvalues
agree at every good prime. -/
theorem Newform.level_eq_of_forall_notMem_prime_eigenvalue_eq {M : ℕ} [NeZero M]
    (f : Newform N k) (g : Newform M k)
    (hχ : f.χ.comp (ZMod.unitsMap (Nat.dvd_lcm_left N M)) =
      g.χ.comp (ZMod.unitsMap (Nat.dvd_lcm_right N M))) {S : Finset ℕ}
    (h : ∀ (p : ℕ) (hp : p.Prime) (hpN : p.Coprime N) (hpM : p.Coprime M), p ∉ S →
      f.eigenvalue ⟨p, hp.pos⟩ hpN = g.eigenvalue ⟨p, hp.pos⟩ hpM) :
    N = M := by
  by_contra hNM
  by_cases hMN : M ∣ N
  · refine false_of_not_dvd g f ?_ (fun p hp hpM hpN hpS ↦ (h p hp hpN hpM hpS).symm)
      fun hNM' ↦ hNM (Nat.dvd_antisymm hNM' hMN)
    rw [← ZMod.unitsMap_comp (Nat.dvd_lcm_right N M) (Nat.lcm_comm N M).dvd,
      ← ZMod.unitsMap_comp (Nat.dvd_lcm_left N M) (Nat.lcm_comm N M).dvd,
      ← MonoidHom.comp_assoc, ← MonoidHom.comp_assoc, hχ]
  · exact false_of_not_dvd f g hχ h hMN

end HeckeRing.GL2
