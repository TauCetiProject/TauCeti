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

The agreement extends from the complement of the finite set to every good index
(`EigenformAwayFromLevel.eigenvalue_eq_of_forall_notMem`), so the difference of the two underlying
cusp forms is a good Hecke eigenvector with `a₁ = 0`; its coefficients therefore vanish at every
index coprime to `N`, so it is old by the Main Lemma
(`TauCeti.mem_cuspFormsOld_of_forall_coprime_qExpansion_coeff_eq_zero`). Being a difference of
newforms it is also new, and old and new are disjoint, so it is zero.

Miyake states the theorem on the Fourier coefficients rather than the eigenvalues; for a
normalised newform the coefficient at a good index *is* the eigenvalue there
(`Newform.qExpansion_coeff_eq_eigenvalue`), so that form is a corollary.

## Main results

* `HeckeRing.GL2.Newform.eq_of_forall_notMem_eigenvalue_eq`: strong multiplicity one, on the
  eigenvalues.
* `HeckeRing.GL2.Newform.eq_of_forall_notMem_qExpansion_coeff_eq`: Miyake's own form, on the
  `q`-expansion coefficients.

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

* [T. Miyake, *Modular forms*][miyake1989], Theorem 4.6.12.
* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005],
  Theorem 5.8.2 (the `∀ n` coprime version; the strong form is deferred to Miyake).
-/

public section

open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup TauCeti

open scoped MatrixGroups

namespace HeckeRing.GL2

variable {N : ℕ} [NeZero N] {k : ℤ}

/-- **The difference of two newforms with the same eigenvalue system is a ring eigenvector at
every good prime**, with that shared eigenvalue. At a prime the ring generator acts as the
classical operator on each of `f` and `g`, and the two eigenvalues agree by hypothesis, so the
difference is scaled by the common value. -/
private theorem exists_heckeRingHomCuspCharSpace_sub_eq_smul {f g : Newform N k}
    (hall : ∀ (n : ℕ+) (hn : Nat.Coprime n N), f.eigenvalue n hn = g.eigenvalue n hn)
    {d : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hd : d = f.toCuspForm - g.toCuspForm)
    (hdχ : d ∈ cuspFormCharSpace k f.χ) (p : ℕ) (hp : p.Prime) (hpN : Nat.Coprime p N) :
    ∃ c : ℂ, heckeRingHomCuspCharSpace k f.χ (heckeTCompositeGamma0 N p) ⟨d, hdχ⟩
      = c • ⟨d, hdχ⟩ := by
  have : NeZero p := ⟨hp.ne_zero⟩
  refine ⟨f.eigenvalue ⟨p, hp.pos⟩ hpN, Subtype.ext ?_⟩
  have hf' := congrArg Subtype.val (f.isEigen ⟨p, hp.pos⟩ hpN)
  have hg' := congrArg Subtype.val (g.isEigen ⟨p, hp.pos⟩ hpN)
  simp only [PNat.mk_coe, heckeTCompositeGamma0_prime N hp,
    heckeRingHomCuspCharSpace_heckeTGeneratorGamma0 k _ hp, LinearMap.coe_restrict_apply,
    Submodule.coe_smul] at hf' hg' ⊢
  rw [hd, map_sub, hf', hg', ← hall ⟨p, hp.pos⟩ hpN, smul_sub]

/-- **Strong multiplicity one** (Miyake, Theorem 4.6.12, fixed level and nebentypus): two
newforms of level `N`, weight `k` and the same nebentypus whose eigenvalues agree at every index
coprime to `N` outside a finite set are equal. -/
theorem Newform.eq_of_forall_notMem_eigenvalue_eq {f g : Newform N k} (hχ : f.χ = g.χ)
    {S : Finset ℕ}
    (h : ∀ (n : ℕ+) (hn : Nat.Coprime n N), (n : ℕ) ∉ S → f.eigenvalue n hn = g.eigenvalue n hn) :
    f = g := by
  -- the eigenvalues agree at every good index
  have hall : ∀ (n : ℕ+) (hn : Nat.Coprime n N), f.eigenvalue n hn = g.eigenvalue n hn :=
    fun n hn ↦ EigenformAwayFromLevel.eigenvalue_eq_of_forall_notMem h hn
  -- the difference is a good Hecke eigenvector with `a₁ = 0`
  set d : CuspForm ((Gamma1 N).map (mapGL ℝ)) k := f.toCuspForm - g.toCuspForm with hd
  have hdχ : d ∈ cuspFormCharSpace k f.χ :=
    Submodule.sub_mem _ f.mem_charSpace (hχ ▸ g.mem_charSpace)
  have heig := fun p hp hpN ↦
    exists_heckeRingHomCuspCharSpace_sub_eq_smul hall hd hdχ p hp hpN
  have h1 : (qExpansion 1 d).coeff 1 = 0 := by
    rw [hd, FunLike.coe_sub,
      ModularForm.qExpansion_sub one_pos (one_mem_strictPeriods_Gamma1_map _), map_sub, f.isNorm,
      g.isNorm, sub_self]
  -- so its coefficients vanish off `N`, and it is old; it is also new, hence zero
  have hd0 : d = 0 :=
    eq_zero_of_forall_prime_heckeRingHomCusp_of_one_eq_zero_of_mem_cuspFormsNew
      (F := ⟨d, hdχ⟩) heig h1 (Submodule.sub_mem _ f.isNew g.isNew)
  exact Newform.ext (sub_eq_zero.mp hd0)

/-- **Strong multiplicity one, on Fourier coefficients** (Miyake's own form of Theorem 4.6.12):
two newforms of level `N`, weight `k` and the same nebentypus whose `q`-expansion coefficients
agree at every index coprime to `N` outside a finite set are equal. For a normalised newform the
coefficient at a good index *is* the eigenvalue there
(`HeckeRing.GL2.Newform.qExpansion_coeff_eq_eigenvalue`), so this is the eigenvalue form. -/
theorem Newform.eq_of_forall_notMem_qExpansion_coeff_eq {f g : Newform N k} (hχ : f.χ = g.χ)
    {S : Finset ℕ}
    (h : ∀ (n : ℕ+), Nat.Coprime (n : ℕ) N → (n : ℕ) ∉ S →
      (qExpansion 1 f.toCuspForm).coeff (n : ℕ) = (qExpansion 1 g.toCuspForm).coeff (n : ℕ)) :
    f = g :=
  Newform.eq_of_forall_notMem_eigenvalue_eq hχ fun n hn hnS ↦ by
    rw [← f.qExpansion_coeff_eq_eigenvalue n hn, ← g.qExpansion_coeff_eq_eigenvalue n hn]
    exact h n hn hnS

end HeckeRing.GL2
