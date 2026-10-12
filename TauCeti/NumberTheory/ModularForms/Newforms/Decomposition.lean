/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Eigenspace.JointEigenvector.Basic
public import TauCeti.NumberTheory.ModularForms.Newforms.OrthogonalBasis

/-!
# Level-raised newforms span the cusp forms

Every cusp form of level `Γ₁(N)` is a linear combination of forms `V_d g`, `(V_d g)(τ) = g(dτ)`,
with `g` a newform of some level `M` and `d * M ∣ N`. This is the spanning half of
Diamond–Shurman's Theorem 5.8.3, the decomposition

```text
S_k(Γ₁(N)) = ⊕_{M ∣ N} ⊕_{f newform of level M} ⊕_{d ∣ N/M} ℂ · f(dτ).
```

The eigenvalue-refined spanning theorem says that a cusp form of level `Γ₁(N)` that is an
eigenvector of every `Tₚ` with `p ∤ N` is a combination of those `V_d g` whose newform `g` has
the same eigenvalues at these primes. In particular a good Hecke
eigenform of level `N` shares its eigenvalues at the primes not dividing `N` with a newform of
some level `M ∣ N`. This is the eigenvalue half of the existence of the newform associated with
an eigenform (Diamond–Shurman, Proposition 5.8.4; Miyake, Corollary 4.6.20). Uniqueness of that
newform, and hence the statement that the eigenform lies in the span of the `V_d g` for a single
`g`, needs strong multiplicity one across levels and is not proved here.

Inside the nebentypus space of a newform `f` of level `N` the spanning theorem does close up: a
good Hecke eigenvector `F ∈ S_k(N, χ_f)` with the eigenvalues of `f` is the multiple `a₁(F) • f`
of `f` (`Newform.eq_qExpansion_coeff_one_smul_of_forall_prime_heckeTCuspNat_eq_smul`, the
whole-space form of Diamond–Shurman's Theorem 5.8.2). The level-raised newforms spanning `F` with
compatible nebentypus have level `N` by the divisor-level rigidity
`Newform.level_eq_of_dvd_of_forall_prime_eigenvalue_eq`, hence are `f` by strong multiplicity
one, and the others lie in nebentypus spaces meeting `S_k(N, χ_f)` only in `0`.

## Main results

* `HeckeRing.GL2.Newform.span_levelRaise_eq_top`: the level-raised newforms span `S_k(Γ₁(N))`.
* `HeckeRing.GL2.Newform.mem_span_levelRaise_of_forall_heckeTCuspNat_eq_smul`: a simultaneous
  eigenvector of the good `Tₚ` lies in the span of the level-raised newforms with its
  eigenvalues.
* `HeckeRing.GL2.Newform.exists_newform_eigenvalue_eq_of_forall_heckeTCuspNat_eq_smul` and
  `HeckeRing.GL2.EigenformAwayFromLevel.exists_newform_eigenvalue_eq`: a nonzero simultaneous
  eigenvector of the good `Tₚ`, in particular a good Hecke eigenform, shares its eigenvalues at
  the primes not dividing the level with a newform of divisor level.
* `HeckeRing.GL2.Newform.eq_qExpansion_coeff_one_smul_of_forall_prime_heckeTCuspNat_eq_smul`: a
  good Hecke eigenvector of `S_k(N, χ)` with the eigenvalues of a newform `f` of level `N` and
  nebentypus `χ` is the multiple `a₁ • f` of `f`.

## Provenance

The last statement is that of `strongMultiplicityOne_constMul` in the AINTLIB `LeanModularForms`
project (Chris Birkbeck, Apache-2.0, <https://github.com/CBirkbeck/AINTLIB> @ `2baa76f742bd`),
`projects/LeanModularForms/LeanModularForms/StrongMultiplicityOne/ConstantMultiple.lean`: a
newform and a good Hecke eigenform sharing eigenvalues are proportional. It is proved here
independently, from the spanning theorem, the divisor-level rigidity of the level and the
independence of the nebentypus spaces.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005],
  Theorem 5.8.2, Theorem 5.8.3 and Proposition 5.8.4.
* [T. Miyake, *Modular forms*][miyake1989], Theorem 4.6.13 and Corollary 4.6.20.
-/

public section

open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup

open scoped MatrixGroups

namespace HeckeRing.GL2

open TauCeti _root_.CuspForm

variable {N : ℕ} {k : ℤ}

namespace Newform

/-- **The level-raised newforms span `S_k(Γ₁(N))`** (Diamond–Shurman, Theorem 5.8.3, spanning):
every cusp form of level `Γ₁(N)` is a combination of forms `V_d g`, `(V_d g)(τ) = g(dτ)`, with `g`
a newform of some level `M` and `d * M ∣ N`. The `NeZero` binders only make the instances
available; they follow from `d * M ∣ N`. -/
theorem span_levelRaise_eq_top (N : ℕ) [NeZero N] (k : ℤ) :
    Submodule.span ℂ {F : CuspForm ((Gamma1 N).map (mapGL ℝ)) k |
      ∃ (M d : ℕ) (_ : NeZero M) (_ : NeZero d) (h : d * M ∣ N) (g : Newform M k),
        CuspForm.levelRaise d (Gamma1_map_le_conjAct_scaleGL_of_dvd h) g.toCuspForm = F} = ⊤ := by
  set S := Submodule.span ℂ {F : CuspForm ((Gamma1 N).map (mapGL ℝ)) k |
      ∃ (M d : ℕ) (_ : NeZero M) (_ : NeZero d) (h : d * M ∣ N) (g : Newform M k),
        CuspForm.levelRaise d (Gamma1_map_le_conjAct_scaleGL_of_dvd h) g.toCuspForm = F}
  -- the image under `V_d` of the new subspace of level `M` is spanned by level-raised newforms
  have hnew (M d : ℕ) [NeZero M] [NeZero d] (h : d * M ∣ N) :
      (cuspFormsNew M k).map (CuspForm.levelRaiseₗ d (Gamma1_map_le_conjAct_scaleGL_of_dvd h)) ≤
        S := by
    rw [← span_range_toCuspForm_eq_cuspFormsNew, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
    exact Submodule.subset_span ⟨M, d, inferInstance, inferInstance, h, g,
      (CuspForm.levelRaiseₗ_apply _ _ _).symm⟩
  refine eq_top_iff.mpr ((sup_cuspFormsOld_cuspFormsNew_eq_top N k).ge.trans (sup_le ?_ ?_))
  · rw [← cuspFormsOldMultiples_one_eq_cuspFormsOld]
    refine cuspFormsOldMultiples_le fun M d h _ _ g hg ↦ ?_
    have : NeZero d := NeZero.of_dvd (dvd_of_mul_right_dvd h)
    have : NeZero M := NeZero.of_dvd (dvd_of_mul_left_dvd h)
    simpa using hnew M d h (Submodule.mem_map_of_mem hg)
  · have h : 1 * N ∣ N := (one_mul N).symm ▸ dvd_rfl
    intro f hf
    -- a form of level `N` is its own level-raise `V₁`
    have hf' := hnew N 1 h (Submodule.mem_map_of_mem hf)
    rwa [CuspForm.levelRaiseₗ_apply, _root_.CuspForm.levelRaise_one_self] at hf'

/-- **A simultaneous eigenvector of the good Hecke operators lies in the span of the level-raised
newforms with its eigenvalues.** If a cusp form `F` of level `Γ₁(N)` satisfies `Tₚ F = aₚ F` at
every prime `p ∤ N`, then `F` is a combination of forms `V_d g`, `d * M ∣ N`, with `g` a newform
of level `M` whose eigenvalue at every prime `p ∤ N` is `aₚ`. -/
theorem mem_span_levelRaise_of_forall_heckeTCuspNat_eq_smul [NeZero N]
    {F : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} {a : ∀ p : ℕ, p.Prime → Nat.Coprime p N → ℂ}
    (hF : ∀ (p : ℕ) (hp : p.Prime) (hpN : Nat.Coprime p N),
      heckeTCuspNat k p (_hn := ⟨hp.ne_zero⟩) F = a p hp hpN • F) :
    F ∈ Submodule.span ℂ {G : CuspForm ((Gamma1 N).map (mapGL ℝ)) k |
      ∃ (M d : ℕ) (_ : NeZero M) (_ : NeZero d) (h : d * M ∣ N) (g : Newform M k),
        (∀ (p : ℕ) (hp : p.Prime) (hpN : Nat.Coprime p N),
          g.eigenvalue ⟨p, hp.pos⟩ (hpN.coprime_dvd_right (dvd_of_mul_left_dvd h)) = a p hp hpN) ∧
        CuspForm.levelRaise d (Gamma1_map_le_conjAct_scaleGL_of_dvd h) g.toCuspForm = G} := by
  -- the good primes, the operators `Tₚ` on them, and the level-raised newforms with a
  -- prescribed eigenvalue system on them
  let ι := {p : ℕ // p.Prime ∧ Nat.Coprime p N}
  let T : ι → Module.End ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) := fun p ↦
    heckeTCuspNat k p.1 (_hn := ⟨p.2.1.ne_zero⟩)
  let S : (ι → ℂ) → Submodule ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) := fun χ ↦
    Submodule.span ℂ {G | ∃ (M d : ℕ) (_ : NeZero M) (_ : NeZero d) (h : d * M ∣ N)
      (g : Newform M k), (∀ p : ι, g.eigenvalue ⟨p.1, p.2.1.pos⟩
        (p.2.2.coprime_dvd_right (dvd_of_mul_left_dvd h)) = χ p) ∧
      CuspForm.levelRaise d (Gamma1_map_le_conjAct_scaleGL_of_dvd h) g.toCuspForm = G}
  -- each `V_d g` is a simultaneous eigenvector, with the eigenvalues of `g`
  have hS (χ : ι → ℂ) : S χ ≤ ⨅ p, (T p).eigenspace (χ p) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨M, d, _, _, h, g, hg, rfl⟩
    refine Submodule.mem_iInf _ |>.mpr fun p ↦ Module.End.mem_eigenspace_iff.mpr ?_
    simp only [T]
    rw [g.heckeTCuspNat_levelRaise_eq_eigenvalue_smul h p.2.1 p.2.2, hg p]
  -- the spaces `S χ` together span everything
  have htop : ⨆ χ, S χ = ⊤ := by
    refine eq_top_iff.mpr ((span_levelRaise_eq_top N k).ge.trans (Submodule.span_le.mpr ?_))
    rintro _ ⟨M, d, _, _, h, g, rfl⟩
    exact Submodule.mem_iSup_of_mem (fun p : ι ↦ g.eigenvalue ⟨p.1, p.2.1.pos⟩
      (p.2.2.coprime_dvd_right (dvd_of_mul_left_dvd h)))
      (Submodule.subset_span ⟨M, d, inferInstance, inferInstance, h, g, fun _ ↦ rfl, rfl⟩)
  -- split off the component of `F` with the eigenvalues `a`; the rest is an eigenvector for `a`
  -- lying in the span of the other joint eigenspaces, hence zero
  let a' : ι → ℂ := fun p ↦ a p.1 p.2.1 p.2.2
  have hFmem : F ∈ ⨆ χ, S χ := htop ▸ Submodule.mem_top
  rw [iSup_split_single S a'] at hFmem
  obtain ⟨s, hs, t, ht, rfl⟩ := Submodule.mem_sup.mp hFmem
  have hsF : s + t ∈ ⨅ p, (T p).eigenspace (a' p) :=
    Submodule.mem_iInf _ |>.mpr fun p ↦ Module.End.mem_eigenspace_iff.mpr (hF p.1 p.2.1 p.2.2)
  have ht' : t ∈ ⨅ p, (T p).eigenspace (a' p) := by
    simpa using Submodule.sub_mem _ hsF (hS a' hs)
  have ht0 : t = 0 := (Submodule.disjoint_def.mp (iSupIndep_iInf_eigenspace T a')) t ht'
    (iSup₂_mono (fun χ _ ↦ hS χ) ht)
  rw [ht0, add_zero]
  refine Submodule.span_mono ?_ hs
  rintro _ ⟨M, d, _, _, h, g, hg, rfl⟩
  exact ⟨M, d, inferInstance, inferInstance, h, g, fun p hp hpN ↦ hg ⟨p, hp, hpN⟩, rfl⟩

/-- **A nonzero simultaneous eigenvector of the good Hecke operators has the eigenvalues of a
newform of divisor level.** If a nonzero cusp form `F` of level `Γ₁(N)` satisfies `Tₚ F = aₚ F`
at every prime `p ∤ N`, then some newform `g` of some level `M ∣ N` has eigenvalue `aₚ` at every
prime `p ∤ N`. -/
theorem exists_newform_eigenvalue_eq_of_forall_heckeTCuspNat_eq_smul [NeZero N]
    {F : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hF0 : F ≠ 0)
    {a : ∀ p : ℕ, p.Prime → Nat.Coprime p N → ℂ}
    (hF : ∀ (p : ℕ) (hp : p.Prime) (hpN : Nat.Coprime p N),
      heckeTCuspNat k p (_hn := ⟨hp.ne_zero⟩) F = a p hp hpN • F) :
    ∃ (M : ℕ) (_ : NeZero M) (hM : M ∣ N) (g : Newform M k),
      ∀ (p : ℕ) (hp : p.Prime) (hpN : Nat.Coprime p N),
        g.eigenvalue ⟨p, hp.pos⟩ (hpN.coprime_dvd_right hM) = a p hp hpN := by
  by_contra hne
  -- with no such newform, the span containing `F` is spanned by the empty set
  refine hF0 ((Submodule.mem_bot ℂ).mp ?_)
  convert mem_span_levelRaise_of_forall_heckeTCuspNat_eq_smul hF using 2
  refine (Submodule.span_eq_bot.mpr ?_).symm
  rintro _ ⟨M, d, _, _, h, g, hg, rfl⟩
  exact absurd ⟨M, inferInstance, dvd_of_mul_left_dvd h, g, hg⟩ hne

end Newform

/-- **A good Hecke eigenform has the eigenvalues of a newform of divisor level**: for a good
Hecke eigenform `f` of level `N` there are a divisor `M` of `N` and a newform `g` of level `M`
whose eigenvalue at every prime `p ∤ N` equals that of `f`. This is the eigenvalue half of the
existence of the newform associated with `f` (Diamond–Shurman, Proposition 5.8.4; Miyake,
Corollary 4.6.20); the uniqueness of `g` is a separate statement. -/
theorem EigenformAwayFromLevel.exists_newform_eigenvalue_eq [NeZero N]
    (f : EigenformAwayFromLevel N k) :
    ∃ (M : ℕ) (_ : NeZero M) (hM : M ∣ N) (g : Newform M k),
      ∀ (p : ℕ) (hp : p.Prime) (hpN : Nat.Coprime p N),
        g.eigenvalue ⟨p, hp.pos⟩ (hpN.coprime_dvd_right hM) = f.eigenvalue ⟨p, hp.pos⟩ hpN :=
  Newform.exists_newform_eigenvalue_eq_of_forall_heckeTCuspNat_eq_smul f.ne_zero
    fun _ hp hpN ↦ f.heckeTCuspNat_eq_eigenvalue_smul hp hpN

/-! ### The good eigensystem of a newform spans a line in its nebentypus space -/

/-- **A good Hecke eigenvector of `S_k(N, χ)` with the eigenvalues of a newform `f` is the
multiple `a₁(F) • f` of `f`** (Diamond–Shurman, Theorem 5.8.2, on the whole nebentypus space
rather than its new part): if `F ∈ S_k(N, χ_f)` satisfies `Tₚ F = λₚ(f) • F` at every prime
`p ∤ N`, then `F = a₁(F) • f`. So the simultaneous eigenspace of the good `Tₚ` in `S_k(N, χ_f)`
for the eigensystem of `f` is the line spanned by `f`. -/
theorem Newform.eq_qExpansion_coeff_one_smul_of_forall_prime_heckeTCuspNat_eq_smul [NeZero N]
    (f : Newform N k) {F : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hF : F ∈ cuspFormCharSpace k f.χ)
    (h : ∀ (p : ℕ) (hp : p.Prime) (hpN : Nat.Coprime p N),
      heckeTCuspNat k p (_hn := ⟨hp.ne_zero⟩) F = f.eigenvalue ⟨p, hp.pos⟩ hpN • F) :
    F = (qExpansion 1 F).coeff 1 • f.toCuspForm := by
  -- `F` is a combination of level-raised newforms with the eigenvalues of `f`; each generator is
  -- a multiple of `f`, or lies in another nebentypus space
  have hFmem : F ∈ (ℂ ∙ f.toCuspForm) ⊔
      ⨆ (ψ : (ZMod N)ˣ →* ℂˣ) (_ : ψ ≠ f.χ), cuspFormCharSpace k ψ := by
    refine Submodule.span_le.mpr ?_ (Newform.mem_span_levelRaise_of_forall_heckeTCuspNat_eq_smul h)
    rintro _ ⟨M, d, _, _, hdM, g, hg, rfl⟩
    have hMN : M ∣ N := dvd_of_mul_left_dvd hdM
    by_cases hgχ : g.χ.comp (ZMod.unitsMap hMN) = f.χ
    · -- compatible nebentypus: `g` has level `N`, so `g = f` and the generator is `V₁ f = f`
      refine Submodule.mem_sup_left ?_
      obtain rfl := f.level_eq_of_dvd_of_forall_prime_eigenvalue_eq g.toEigenformAwayFromLevel
        (ne_of_eq_of_ne g.isNorm one_ne_zero) hMN hgχ hg
      obtain rfl : d = 1 :=
        (mul_left_eq_self₀.mp (Nat.dvd_antisymm hdM (dvd_mul_left _ _))).resolve_right
          (NeZero.ne _)
      rw [ZMod.unitsMap_self, MonoidHom.comp_id] at hgχ
      rw [_root_.CuspForm.levelRaise_one_self, Newform.eq_of_forall_prime_eigenvalue_eq hgχ hg]
      exact Submodule.mem_span_singleton_self _
    · -- otherwise the generator lies in the nebentypus space of `g`, which is not `χ_f`
      exact Submodule.mem_sup_right (Submodule.mem_iSup_of_mem _ (Submodule.mem_iSup_of_mem hgχ
        (CuspForm.levelRaise_mem_cuspFormCharSpace_of_dvd hdM g.χ g.mem_charSpace)))
  -- the component in the other nebentypus spaces is `F - c • f ∈ S_k(N, χ)`, hence zero
  obtain ⟨s, hs, t, ht, rfl⟩ := Submodule.mem_sup.mp hFmem
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hs
  have htχ : t ∈ cuspFormCharSpace k f.χ := by
    have := Submodule.sub_mem _ hF (Submodule.smul_mem _ c f.mem_charSpace)
    rwa [add_sub_cancel_left] at this
  have ht0 : t = 0 :=
    (Submodule.disjoint_def.mp (iSupIndep_def.mp (iSupIndep_cuspFormCharSpace k) f.χ)) t htχ ht
  -- the scalar is the first coefficient, as `a₁(f) = 1`
  rw [ht0, add_zero, FunLike.coe_smul,
    ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods_Gamma1_map _),
    PowerSeries.coeff_smul, f.isNorm, smul_eq_mul, mul_one]

end HeckeRing.GL2
