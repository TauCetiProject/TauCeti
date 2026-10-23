/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Newforms.EigenvectorVanishing
public import TauCeti.NumberTheory.ModularForms.Newforms.EigenvalueExtension
public import TauCeti.NumberTheory.ModularForms.Newforms.Coefficient

/-!
# Strong multiplicity one, at fixed level and nebentypus

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

## Provenance

Adapted from the AINTLIB `LeanModularForms` project (Chris Birkbeck, Apache-2.0,
<https://github.com/CBirkbeck/AINTLIB> @ `2baa76f742bd`),
`projects/LeanModularForms/LeanModularForms/StrongMultiplicityOne/ConstantMultiple.lean` —
declaration `strongMultiplicityOne`. The source routes through
`strongMultiplicityOne_constMul` (a newform and an eigenform sharing eigenvalues are
proportional, with `a₁ = 1` pinning the constant); here the difference is shown to be zero
directly from the Main Lemma and the disjointness of the old and new subspaces, so the
proportionality step is not needed.

## References

* [T. Miyake, *Modular forms*][miyake1989], Theorem 4.6.12, and Theorem 4.6.19 for the
  cross-level statement.
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

end HeckeRing.GL2
