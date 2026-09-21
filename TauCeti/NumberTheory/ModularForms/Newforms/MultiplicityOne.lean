/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Newforms.EigenvectorVanishing

/-!
# Multiplicity one on the new part of `S_k(N, χ)`

A cusp form in the new part of `S_k(N, χ)` that is an eigenvector of the Hecke ring at every
prime not dividing `N` is determined, up to a scalar, by those eigenvalues. Equivalently: each
simultaneous eigenspace of the good Hecke operators inside `S_k(N, χ)ⁿᵉʷ` is at most
one-dimensional, and is a line as soon as it is nonzero.

It rests on `eq_zero_of_forall_prime_heckeRingHomCusp_of_one_eq_zero_of_mem_cuspFormsNew`
(`Newforms/EigenvectorVanishing.lean`): such an eigenvector with `a₁ = 0` is zero. Scaling each
of the two eigenvectors by the other's first coefficient and subtracting produces exactly such
an eigenvector.

## Main results

* `HeckeRing.GL2.smul_eq_smul_of_forall_prime_heckeRingHomCusp_of_mem_cuspFormsNew`: two good
  Hecke eigenvectors in the new part sharing their eigenvalues satisfy `a₁(g) • f = a₁(f) • g`.
* `HeckeRing.GL2.exists_eq_smul_of_forall_prime_heckeRingHomCusp_of_mem_cuspFormsNew`: the same
  conclusion as proportionality — if one of them is nonzero, the other is a scalar multiple of
  it.
* `HeckeRing.GL2.cuspFormsNewEigenspace`: that simultaneous eigenspace, as a submodule, with
  `HeckeRing.GL2.cuspFormsNewEigenspace_def` and
  `HeckeRing.GL2.mem_cuspFormsNewEigenspace_iff`.
* `HeckeRing.GL2.finrank_cuspFormsNewEigenspace_le_one` and
  `HeckeRing.GL2.finrank_cuspFormsNewEigenspace_eq_one`: multiplicity one in dimensional form —
  the eigenspace has dimension at most one, and exactly one once it contains a nonzero form.

## References

* [T. Miyake, *Modular forms*][miyake1989], Theorem 4.6.13(1).
* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005],
  Theorem 5.8.2.
-/

public section

open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup TauCeti

open scoped MatrixGroups

namespace HeckeRing.GL2

variable {N : ℕ} [NeZero N] {k : ℤ} {χ : (ZMod N)ˣ →* ℂˣ}

/-- **Multiplicity one on the new part of `S_k(N, χ)`** (Miyake, Theorem 4.6.13(1)): two cusp
forms in the new part that are eigenvectors of the Hecke ring at every prime not dividing `N`,
*with the same eigenvalue at each such prime*, are proportional: `a₁(g) • f = a₁(f) • g`. So each
simultaneous eigenspace of the good Hecke operators inside the new part is at most
one-dimensional. -/
theorem smul_eq_smul_of_forall_prime_heckeRingHomCusp_of_mem_cuspFormsNew
    {f g : cuspFormCharSpace k χ}
    (ha : ∀ p : ℕ, p.Prime → Nat.Coprime p N → ∃ c : ℂ,
      heckeRingHomCuspCharSpace k χ (heckeTCompositeGamma0 N p) f = c • f ∧
        heckeRingHomCuspCharSpace k χ (heckeTCompositeGamma0 N p) g = c • g)
    (hf : (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ∈ cuspFormsNew N k)
    (hg : (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ∈ cuspFormsNew N k) :
    (qExpansion 1 (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff 1 •
        (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) =
      (qExpansion 1 (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff 1 •
        (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) := by
  set a := (qExpansion 1 (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff 1 with hadef
  set b := (qExpansion 1 (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff 1 with hbdef
  -- the one place the `Submodule` coercion has to be pushed through the combination
  have hcoe : ((b • f - a • g : cuspFormCharSpace k χ) :
      CuspForm ((Gamma1 N).map (mapGL ℝ)) k) =
      b • (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) -
        a • (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) := by
    rw [Submodule.coe_sub, Submodule.coe_smul, Submodule.coe_smul]
  -- the combination `b • f - a • g` is a good eigenvector in the new part with `a₁ = 0`
  have key : ((b • f - a • g : cuspFormCharSpace k χ) :
      CuspForm ((Gamma1 N).map (mapGL ℝ)) k) = 0 := by
    refine eq_zero_of_forall_prime_heckeRingHomCusp_of_one_eq_zero_of_mem_cuspFormsNew
      (fun p hp hpN ↦ ?_) ?_ ?_
    · obtain ⟨c, hcf, hcg⟩ := ha p hp hpN
      exact ⟨c, by rw [map_sub, map_smul, map_smul, hcf, hcg, smul_sub, smul_comm c b,
        smul_comm c a]⟩
    · rw [← CuspForm.qExpansionCoeffₗ_apply one_pos (one_mem_strictPeriods_Gamma1_map N), hcoe,
        map_sub, map_smul, map_smul, CuspForm.qExpansionCoeffₗ_apply,
        CuspForm.qExpansionCoeffₗ_apply, ← hadef, ← hbdef, smul_eq_mul, smul_eq_mul]
      ring
    · exact Submodule.sub_mem _ (Submodule.smul_mem _ _ hf) (Submodule.smul_mem _ _ hg)
  rw [hcoe, sub_eq_zero] at key
  exact key

/-- **Two good Hecke eigenvectors in the new part are proportional**, in the form a consumer
wants: if `f` is nonzero, every `g` sharing its eigenvalues is a scalar multiple of it. So a
simultaneous eigenspace of the good Hecke operators inside the new part of `S_k(N, χ)` is
spanned by any one of its nonzero vectors, which is one-dimensionality in concrete form.

The nonvanishing hypothesis is only on `f`: the case `a₁(f) = 0` is not an exception to be
excluded but is impossible once `f ≠ 0`, by
`eq_zero_of_forall_prime_heckeRingHomCusp_of_one_eq_zero_of_mem_cuspFormsNew`. -/
theorem exists_eq_smul_of_forall_prime_heckeRingHomCusp_of_mem_cuspFormsNew
    {f g : cuspFormCharSpace k χ}
    (ha : ∀ p : ℕ, p.Prime → Nat.Coprime p N → ∃ c : ℂ,
      heckeRingHomCuspCharSpace k χ (heckeTCompositeGamma0 N p) f = c • f ∧
        heckeRingHomCuspCharSpace k χ (heckeTCompositeGamma0 N p) g = c • g)
    (hf : (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ∈ cuspFormsNew N k)
    (hg : (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ∈ cuspFormsNew N k)
    (hf0 : (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ≠ 0) :
    ∃ c : ℂ, (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) =
      c • (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) := by
  have ha0 : (qExpansion 1 (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff 1 ≠ 0 := fun h ↦
    hf0 (eq_zero_of_forall_prime_heckeRingHomCusp_of_one_eq_zero_of_mem_cuspFormsNew
      (fun p hp hpN ↦ (ha p hp hpN).imp fun _ hc ↦ hc.1) h hf)
  refine ⟨((qExpansion 1 (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff 1)⁻¹ *
    (qExpansion 1 (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff 1, ?_⟩
  rw [mul_smul, smul_eq_smul_of_forall_prime_heckeRingHomCusp_of_mem_cuspFormsNew ha hf hg,
    inv_smul_smul₀ ha0]

/-! ### Multiplicity one in dimensional form -/

/-- The **simultaneous eigenspace of the good Hecke operators in the new part** of `S_k(N, χ)`,
for the eigenvalue system `a`: the forms of nebentypus `χ` lying in `S_k(Γ₁(N))ⁿᵉʷ` on which `Tₙ`
acts by the scalar `a n hn`, at every index `n` coprime to `N`.

The eigenvalue system is a *dependent* function of the good index and its coprimality proof, the
spelling `EigenformAwayFromLevel.eigenvalue` uses, so that every value of `a` is used. The index
runs over `ℕ+`, also as there: at `N = 1` the natural number `0` is coprime to `N`, and `T₀` is the
identity, so a `ℕ`-indexed system would impose a spurious constraint at that index. -/
noncomputable def cuspFormsNewEigenspace (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (a : ∀ n : ℕ+, Nat.Coprime (n : ℕ) N → ℂ) : Submodule ℂ (cuspFormCharSpace k χ) :=
  (⨅ (n : ℕ+) (hn : Nat.Coprime (n : ℕ) N),
      Module.End.eigenspace (heckeRingHomCuspCharSpace k χ (heckeTCompositeGamma0 N n))
        (a n hn)) ⊓
    (cuspFormsNew N k).comap (cuspFormCharSpace k χ).subtype

/-- Defining equation for the sealed `cuspFormsNewEigenspace`: it is the joint eigenspace of the
good Hecke operators, met with the new subspace. -/
lemma cuspFormsNewEigenspace_def (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (a : ∀ n : ℕ+, Nat.Coprime (n : ℕ) N → ℂ) :
    cuspFormsNewEigenspace k χ a =
      (⨅ (n : ℕ+) (hn : Nat.Coprime (n : ℕ) N),
        Module.End.eigenspace (heckeRingHomCuspCharSpace k χ (heckeTCompositeGamma0 N n))
          (a n hn)) ⊓
      (cuspFormsNew N k).comap (cuspFormCharSpace k χ).subtype := (rfl)

/-- Membership in the simultaneous eigenspace: the good eigenvector equations together with
newness. -/
@[simp]
lemma mem_cuspFormsNewEigenspace_iff {a : ∀ n : ℕ+, Nat.Coprime (n : ℕ) N → ℂ}
    {f : cuspFormCharSpace k χ} :
    f ∈ cuspFormsNewEigenspace k χ a ↔
      (∀ (n : ℕ+) (hn : Nat.Coprime (n : ℕ) N),
          heckeRingHomCuspCharSpace k χ (heckeTCompositeGamma0 N n) f = a n hn • f) ∧
        (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ∈ cuspFormsNew N k := by
  simp [cuspFormsNewEigenspace, Submodule.mem_iInf]

/-- **The simultaneous eigenspace is spanned by any one of its nonzero forms.** This is
`exists_eq_smul_of_forall_prime_heckeRingHomCusp_of_mem_cuspFormsNew` read as a statement about
the eigenspace rather than about a pair of forms. -/
theorem cuspFormsNewEigenspace_le_span_singleton {a : ∀ n : ℕ+, Nat.Coprime (n : ℕ) N → ℂ}
    {f : cuspFormCharSpace k χ}
    (hf : f ∈ cuspFormsNewEigenspace k χ a) (hf0 : f ≠ 0) :
    cuspFormsNewEigenspace k χ a ≤ Submodule.span ℂ {f} := by
  rw [mem_cuspFormsNewEigenspace_iff] at hf
  intro g hg
  rw [mem_cuspFormsNewEigenspace_iff] at hg
  obtain ⟨c, hc⟩ := exists_eq_smul_of_forall_prime_heckeRingHomCusp_of_mem_cuspFormsNew
    (fun p hp hpN ↦ ⟨a ⟨p, hp.pos⟩ hpN, hf.1 ⟨p, hp.pos⟩ hpN, hg.1 ⟨p, hp.pos⟩ hpN⟩) hf.2 hg.2
    (Submodule.coe_eq_zero.not.2 hf0)
  exact Submodule.mem_span_singleton.2 ⟨c, Subtype.ext hc.symm⟩

/-- **Multiplicity one, in dimensional form** (Miyake, Theorem 4.6.13(1)): a simultaneous
eigenspace of the good Hecke operators inside `S_k(N, χ)ⁿᵉʷ` has dimension at most one. -/
theorem finrank_cuspFormsNewEigenspace_le_one (a : ∀ n : ℕ+, Nat.Coprime (n : ℕ) N → ℂ) :
    Module.finrank ℂ (cuspFormsNewEigenspace k χ a) ≤ 1 := by
  rcases eq_or_ne (cuspFormsNewEigenspace k χ a) ⊥ with h | h
  · rw [h, finrank_bot]
    exact Nat.zero_le 1
  · obtain ⟨f, hf, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
    calc Module.finrank ℂ (cuspFormsNewEigenspace k χ a)
        ≤ Module.finrank ℂ (Submodule.span ℂ {f}) :=
          Submodule.finrank_mono (cuspFormsNewEigenspace_le_span_singleton hf hf0)
      _ = 1 := finrank_span_singleton hf0

/-- **Multiplicity one, in dimensional form**: once a simultaneous eigenspace of the good Hecke
operators inside `S_k(N, χ)ⁿᵉʷ` contains a nonzero form, it is a line. -/
theorem finrank_cuspFormsNewEigenspace_eq_one {a : ∀ n : ℕ+, Nat.Coprime (n : ℕ) N → ℂ}
    {f : cuspFormCharSpace k χ}
    (hf : f ∈ cuspFormsNewEigenspace k χ a) (hf0 : f ≠ 0) :
    Module.finrank ℂ (cuspFormsNewEigenspace k χ a) = 1 := by
  have hspan : cuspFormsNewEigenspace k χ a = Submodule.span ℂ {f} :=
    le_antisymm (cuspFormsNewEigenspace_le_span_singleton hf hf0)
      (Submodule.span_le.2 (Set.singleton_subset_iff.2 hf))
  rw [hspan, finrank_span_singleton hf0]

end HeckeRing.GL2

end
