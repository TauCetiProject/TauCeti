/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Nebentypus.Composite
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Nebentypus.EigenFromPrimes
public import TauCeti.NumberTheory.ModularForms.Newforms.Newform

/-!
# Full Hecke eigenforms

A full Hecke eigenform is a nonzero cusp form of nebentypus `χ` that is an eigenvector for
`T_n` at every positive index `n`, including the primes dividing the level. This is the
unqualified notion of eigenform: `EigenformAwayFromLevel` remains the weaker object carrying
only the good-index eigenrelations.

The prime operators determine the full eigensystem. At a good prime the prime-power blocks
satisfy the usual Hecke recurrence; at a prime dividing the level they are powers of `U_p = T_p`.
The coprime multiplication law then combines the prime-power blocks, including a mixture of good
and bad primes.

## Main declarations

* `HeckeRing.GL2.Eigenform`: a nonzero cusp form with nebentypus and eigenvalues at every
  positive index.
* `HeckeRing.GL2.Eigenform.ofForallPrime`: construct a full eigenform from eigenrelations at
  every prime.
* `HeckeRing.GL2.EigenformAwayFromLevel.toEigenform`: upgrade a good Hecke eigenform once the
  missing bad-prime eigenrelations are supplied.
* `HeckeRing.GL2.Eigenform.qExpansion_coeff_eq_eigenvalue_mul_coeff_one`: the coefficient at
  every positive index is its eigenvalue times the first coefficient.

## Provenance

The bundled layout specializes `EigenformAwayFromLevel`, whose shape is adapted from AINTLIB's
`LeanModularForms/HeckeRIngs/GL2/Newforms/Basic.lean` (Chris Birkbeck, commit
`2baa76f742bdb4fb8ee323fabba41203bd390e08`, Apache-2.0). The eigencondition here is redesigned
over Tau Ceti's positive-index `heckeTCompositeGamma0` API and includes the bad indices; the
prime-assembly proof composes Tau Ceti's good-prime recurrence, bad-prime power identity, and
coprime product formula.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005],
  Definition 5.8.1 and Proposition 5.8.5.
* [T. Miyake, *Modular forms*][miyake1989], §4.5.
-/

public section

open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup HeckeRing.GLn

open scoped MatrixGroups ModularForm HeckeCosetModule

namespace HeckeRing.GL2

variable {N : ℕ} [NeZero N] {k : ℤ}

/-- **A full Hecke eigenform.** This is a nonzero cusp form in a fixed nebentypus space together
with its eigenvalue at every positive index. In contrast with `EigenformAwayFromLevel`, no
coprimality condition excludes the primes dividing the level. -/
structure Eigenform (N : ℕ) [NeZero N] (k : ℤ)
    extends CuspForm ((Gamma1 N).map (mapGL ℝ)) k where
  /-- The nebentypus character. -/
  χ : (ZMod N)ˣ →* ℂˣ
  /-- The form transforms under the diamond operators by `χ`. -/
  mem_charSpace : toCuspForm ∈ cuspFormCharSpace k χ
  /-- The eigenvalue at a positive index. -/
  eigenvalue : ℕ+ → ℂ
  /-- The Hecke element `T_n` acts on the form by `eigenvalue n`. -/
  isEigen : ∀ n : ℕ+,
    heckeRingHomCuspCharSpace (k := k) (χ := χ) (heckeTCompositeGamma0 N n.val)
        ⟨toCuspForm, mem_charSpace⟩
      = eigenvalue n • (⟨toCuspForm, mem_charSpace⟩ : cuspFormCharSpace k χ)
  /-- An eigenform is nonzero. -/
  ne_zero : toCuspForm ≠ 0

namespace Eigenform

/-- A full eigenform is, in particular, an eigenform away from the level. -/
noncomputable def toEigenformAwayFromLevel (f : Eigenform N k) : EigenformAwayFromLevel N k where
  toCuspForm := f.toCuspForm
  χ := f.χ
  mem_charSpace := f.mem_charSpace
  eigenvalue n _ := f.eigenvalue n
  isEigen n _ := f.isEigen n
  ne_zero := f.ne_zero

@[simp]
theorem toEigenformAwayFromLevel_toCuspForm (f : Eigenform N k) :
    f.toEigenformAwayFromLevel.toCuspForm = f.toCuspForm := (rfl)

@[simp]
theorem toEigenformAwayFromLevel_χ (f : Eigenform N k) :
    f.toEigenformAwayFromLevel.χ = f.χ := (rfl)

@[simp]
theorem toEigenformAwayFromLevel_eigenvalue (f : Eigenform N k) (n : ℕ+)
    (hn : Nat.Coprime n.val N) :
    f.toEigenformAwayFromLevel.eigenvalue n hn = f.eigenvalue n := (rfl)

/-- **Extensionality.** A full eigenform is determined by its underlying cusp form. The form
determines the nebentypus, and nonvanishing makes every eigenvalue unique. -/
@[ext]
theorem ext {f g : Eigenform N k} (h : f.toCuspForm = g.toCuspForm) : f = g := by
  obtain ⟨F, χf, memf, af, eigf, nzf⟩ := f
  obtain ⟨G, χg, memg, ag, eigg, nzg⟩ := g
  simp only at h
  subst h
  obtain rfl : χf = χg := eq_of_mem_cuspFormCharSpace_of_ne_zero memf memg nzf
  have hx : (⟨F, memf⟩ : cuspFormCharSpace k χf) ≠ 0 := fun hx ↦ nzf (congrArg Subtype.val hx)
  have hae : af = ag := funext fun n ↦
    smul_left_injective ℂ hx ((eigf n).symm.trans (eigg n))
  subst hae
  rfl

/-- **Construct a full eigenform from its prime eigenrelations.** Eigen-ness at every prime
spreads through the prime-power recurrences and coprime multiplication to every positive index. -/
noncomputable def ofForallPrime {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    {χ : (ZMod N)ˣ →* ℂˣ} (hχ : f ∈ cuspFormCharSpace k χ) (hf : f ≠ 0)
    (h : ∀ p : ℕ, p.Prime → ∃ c : ℂ,
      heckeRingHomCuspCharSpace k χ (heckeTGeneratorGamma0 N p) ⟨f, hχ⟩ = c • ⟨f, hχ⟩) :
    Eigenform N k where
  toCuspForm := f
  χ := χ
  mem_charSpace := hχ
  eigenvalue n := (exists_smul_heckeTCompositeGamma0_of_forall_prime h n n.pos.ne').choose
  isEigen n := (exists_smul_heckeTCompositeGamma0_of_forall_prime h n n.pos.ne').choose_spec
  ne_zero := hf

@[simp]
theorem ofForallPrime_toCuspForm {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    {χ : (ZMod N)ˣ →* ℂˣ} (hχ : f ∈ cuspFormCharSpace k χ) (hf : f ≠ 0)
    (h : ∀ p : ℕ, p.Prime → ∃ c : ℂ,
      heckeRingHomCuspCharSpace k χ (heckeTGeneratorGamma0 N p) ⟨f, hχ⟩ = c • ⟨f, hχ⟩) :
    (ofForallPrime hχ hf h).toCuspForm = f := (rfl)

@[simp]
theorem ofForallPrime_χ {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    {χ : (ZMod N)ˣ →* ℂˣ} (hχ : f ∈ cuspFormCharSpace k χ) (hf : f ≠ 0)
    (h : ∀ p : ℕ, p.Prime → ∃ c : ℂ,
      heckeRingHomCuspCharSpace k χ (heckeTGeneratorGamma0 N p) ⟨f, hχ⟩ = c • ⟨f, hχ⟩) :
    (ofForallPrime hχ hf h).χ = χ := (rfl)

/-- At a prime, the classical operator acts on a full eigenform by its stored eigenvalue. -/
theorem heckeTCuspNat_eq_eigenvalue_smul (f : Eigenform N k) {p : ℕ} (hp : p.Prime) :
    heckeTCuspNat k p (_hn := ⟨hp.ne_zero⟩) f.toCuspForm =
      f.eigenvalue ⟨p, hp.pos⟩ • f.toCuspForm := by
  have h := congrArg Subtype.val (f.isEigen ⟨p, hp.pos⟩)
  rw [← coe_heckeRingHomCuspCharSpace_heckeTGeneratorGamma0 k f.χ hp
    (⟨f.toCuspForm, f.mem_charSpace⟩ : cuspFormCharSpace k f.χ)]
  simpa [heckeTCompositeGamma0_prime N hp] using h

/-- **Every positive-index coefficient of a full eigenform is its eigenvalue times `a₁`.**
The first coefficient of `T_n f` is `a_n(f)`, at good and bad indices alike. -/
theorem qExpansion_coeff_eq_eigenvalue_mul_coeff_one (f : Eigenform N k) (n : ℕ+) :
    (qExpansion 1 f.toCuspForm).coeff n =
      f.eigenvalue n * (qExpansion 1 f.toCuspForm).coeff 1 := by
  have h := qExpansion_coeff_heckeRingHomCuspCharSpace_heckeTCompositeGamma0_of_coprime
    n.pos.ne' (⟨f.toCuspForm, f.mem_charSpace⟩ : cuspFormCharSpace k f.χ)
      (Nat.coprime_one_left n)
  rw [f.isEigen n, Submodule.coe_smul, FunLike.coe_smul,
    ModularForm.qExpansion_smul one_pos (TauCeti.one_mem_strictPeriods_Gamma1_map _),
    PowerSeries.coeff_smul, smul_eq_mul] at h
  simpa using h.symm

end Eigenform

namespace EigenformAwayFromLevel

/-- **Upgrade a good Hecke eigenform to a full eigenform from the bad-prime equations.** The
input supplies precisely what `EigenformAwayFromLevel` omits: at every prime dividing the level,
the classical operator `U_p = T_p` acts by a scalar. -/
noncomputable def toEigenform (f : EigenformAwayFromLevel N k)
    (hbad : ∀ (p : ℕ) (hp : p.Prime), p ∣ N → ∃ c : ℂ,
      heckeTCuspNat k p (_hn := ⟨hp.ne_zero⟩) f.toCuspForm = c • f.toCuspForm) :
    Eigenform N k :=
  Eigenform.ofForallPrime f.mem_charSpace f.ne_zero fun p hp ↦ by
    by_cases hpN : Nat.Coprime p N
    · exact ⟨f.eigenvalue ⟨p, hp.pos⟩ hpN, by
        simpa [heckeTCompositeGamma0_prime N hp] using f.isEigen ⟨p, hp.pos⟩ hpN⟩
    · have hpdvd : p ∣ N := by simpa [hp.coprime_iff_not_dvd] using hpN
      obtain ⟨c, hc⟩ := hbad p hp hpdvd
      refine ⟨c, Subtype.ext ?_⟩
      rw [coe_heckeRingHomCuspCharSpace_heckeTGeneratorGamma0 k f.χ hp]
      exact hc

@[simp]
theorem toEigenform_toCuspForm (f : EigenformAwayFromLevel N k)
    (hbad : ∀ (p : ℕ) (hp : p.Prime), p ∣ N → ∃ c : ℂ,
      heckeTCuspNat k p (_hn := ⟨hp.ne_zero⟩) f.toCuspForm = c • f.toCuspForm) :
    (f.toEigenform hbad).toCuspForm = f.toCuspForm := (rfl)

@[simp]
theorem toEigenform_χ (f : EigenformAwayFromLevel N k)
    (hbad : ∀ (p : ℕ) (hp : p.Prime), p ∣ N → ∃ c : ℂ,
      heckeTCuspNat k p (_hn := ⟨hp.ne_zero⟩) f.toCuspForm = c • f.toCuspForm) :
    (f.toEigenform hbad).χ = f.χ := (rfl)

@[simp]
theorem toEigenform_toEigenformAwayFromLevel (f : EigenformAwayFromLevel N k)
    (hbad : ∀ (p : ℕ) (hp : p.Prime), p ∣ N → ∃ c : ℂ,
      heckeTCuspNat k p (_hn := ⟨hp.ne_zero⟩) f.toCuspForm = c • f.toCuspForm) :
    (f.toEigenform hbad).toEigenformAwayFromLevel = f :=
  EigenformAwayFromLevel.ext rfl

@[simp]
theorem toEigenform_eigenvalue (f : EigenformAwayFromLevel N k)
    (hbad : ∀ (p : ℕ) (hp : p.Prime), p ∣ N → ∃ c : ℂ,
      heckeTCuspNat k p (_hn := ⟨hp.ne_zero⟩) f.toCuspForm = c • f.toCuspForm)
    (n : ℕ+) (hn : Nat.Coprime n.val N) :
    (f.toEigenform hbad).eigenvalue n = f.eigenvalue n hn := by
  rw [← Eigenform.toEigenformAwayFromLevel_eigenvalue _ n hn,
    toEigenform_toEigenformAwayFromLevel]

end EigenformAwayFromLevel

end HeckeRing.GL2

end
