/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Eigenspace.JointEigenvector.Basic
public import TauCeti.NumberTheory.ModularForms.Newforms.OrthogonalBasis

import TauCeti.Algebra.DirectSum.Internal
import TauCeti.Data.ZMod.Units
import TauCeti.LinearAlgebra.LinearIndependent.Basic
import TauCeti.LinearAlgebra.Submodule.Independent

/-!
# Level-raised newforms form a basis of the cusp forms

Every cusp form of level `Γ₁(N)` is a unique linear combination of forms `V_d g`,
`(V_d g)(τ) = g(dτ)`, with `g` a newform of some level `M` and `d * M ∣ N`. This is
Diamond–Shurman's Theorem 5.8.3, the decomposition

```text
S_k(Γ₁(N)) = ⊕_{M ∣ N} ⊕_{f newform of level M} ⊕_{d ∣ N/M} ℂ · f(dτ),
```

packaged both as `ℂ`-bases of `S_k(Γ₁(N))` and `S_k(N, χ)` and as internal direct sums of
level-raised new subspaces:

```text
S_k(Γ₁(N)) = ⨁_{M ∣ N} ⨁_{d ∣ N / M} V_d S_k(Γ₁(M))ⁿᵉʷ,
S_k(N, χ)  = ⨁_{cond χ ∣ M ∣ N} ⨁_{d ∣ N / M} V_d S_k(M, χ_M)ⁿᵉʷ.
```

The eigenvalue-refined spanning theorem says that a cusp form of level `Γ₁(N)` that is an
eigenvector of every `Tₚ` with `p ∤ N` is a combination of those `V_d g` whose newform `g` has
the same eigenvalues at these primes. In particular a good Hecke
eigenform of level `N` shares its eigenvalues at the primes not dividing `N` with a newform of
some level `M ∣ N`. This is the eigenvalue half of the existence of the newform associated with
an eigenform (Diamond–Shurman, Proposition 5.8.4; Miyake, Corollary 4.6.20).

Inside the nebentypus space of a newform `f` of level `N` the spanning theorem closes up to a line:
a good Hecke eigenvector `F ∈ S_k(N, χ_f)` with the eigenvalues of `f` is the multiple `a₁(F) • f`
of `f` (`Newform.eq_qExpansion_coeff_one_smul_of_forall_prime_heckeTCuspNat_eq_smul`, the
whole-space form of Diamond–Shurman's Theorem 5.8.2). The level-raised newforms spanning `F` with
compatible nebentypus have level `N` by the divisor-level rigidity
`Newform.level_eq_of_dvd_of_forall_prime_eigenvalue_eq`, hence are `f` by strong multiplicity
one, and the others lie in nebentypus spaces meeting `S_k(N, χ_f)` only in `0`.

Linear independence of the `V_d g` is assembled in three steps: for fixed `(M, g)` via
`CuspForm.linearIndependent_levelRaise`, across distinct `(M, g)` in `S_k(N, χ)` via cross-level
strong multiplicity one (`HeckeRing.GL2.Newform.eigenvalue_injective_of_comp_unitsMap_eq`), and
across characters `χ` via `TauCeti.iSupIndep_cuspFormCharSpace`.

## Main definitions

* `HeckeRing.GL2.Newform.levelRaiseBasis`: the level-raised newforms `V_d g` (`M ∣ N`,
  `d * M ∣ N`), as a `ℂ`-basis of `S_k(Γ₁(N))`.
* `HeckeRing.GL2.Newform.levelRaiseBasisCharSpace`: the level-raised newforms whose nebentypus
  pulls back to `χ`, as a `ℂ`-basis of `S_k(N, χ)`.

## Main results

* `HeckeRing.GL2.Newform.span_levelRaise_eq_top`: the level-raised newforms span `S_k(Γ₁(N))`.
* `HeckeRing.GL2.Newform.iSup_range_levelRaise_le_span_levelRaise`: every cusp form raised to level
  `N` from `S_k(Γ₁(M))` lies in the span of the level-raised newforms of levels dividing `M`.
* `HeckeRing.GL2.Newform.mem_span_levelRaise_of_forall_heckeTCuspNat_eq_smul`: a simultaneous
  eigenvector of the good `Tₚ` lies in the span of the level-raised newforms with its
  eigenvalues.
* `HeckeRing.GL2.Newform.exists_newform_eigenvalue_eq_of_forall_heckeTCuspNat_eq_smul` and
  `HeckeRing.GL2.EigenformAwayFromLevel.exists_newform_eigenvalue_eq`: a nonzero simultaneous
  eigenvector of the good `Tₚ`, in particular a good Hecke eigenform, shares its eigenvalues at
  the primes not dividing the level with a newform of divisor level.
* `Newform.exists_newform_comp_unitsMap_eq_and_eigenvalue_eq_of_forall_heckeTCuspNat_eq_smul`:
  for a nonzero eigenvector in `S_k(N, χ)`, that newform can be chosen with nebentypus inducing `χ`.
* `HeckeRing.GL2.Newform.eq_qExpansion_coeff_one_smul_of_forall_prime_heckeTCuspNat_eq_smul`: a
  good Hecke eigenvector of `S_k(N, χ)` with the eigenvalues of a newform `f` of level `N` and
  nebentypus `χ` is the multiple `a₁ • f` of `f`.
* `HeckeRing.GL2.Newform.linearIndependent_levelRaise_of_comp_unitsMap_eq`,
  `HeckeRing.GL2.Newform.linearIndependent_levelRaise`: linear independence of the level-raised
  newforms at a fixed nebentypus and across all nebentypes.
* `TauCeti.iSup_map_levelRaiseₗ_cuspFormsNew_eq_top`,
  `TauCeti.iSupIndep_map_levelRaiseₗ_cuspFormsNew`,
  `TauCeti.isInternal_map_levelRaiseₗ_cuspFormsNew`: internal direct-sum decomposition of
  `S_k(Γ₁(N))` into `V_d S_k(Γ₁(M))ⁿᵉʷ` over all pairs `(M, d)` with `d * M ∣ N`.
* `TauCeti.iSup_map_levelRaiseₗ_cuspFormsNew_inf_cuspFormCharSpace_eq_cuspFormCharSpace`,
  `TauCeti.iSupIndep_map_levelRaiseₗ_cuspFormsNew_inf_cuspFormCharSpace`,
  `TauCeti.isInternal_comap_map_levelRaiseₗ_cuspFormsNew_inf_cuspFormCharSpace`: the
  fixed-character refinement on `S_k(N, χ)` over pairs `(M, d)` with `d * M ∣ N` and `cond χ ∣ M`.

## Provenance

The proportionality statement
`Newform.eq_qExpansion_coeff_one_smul_of_forall_prime_heckeTCuspNat_eq_smul` is that of
`strongMultiplicityOne_constMul` in the AINTLIB `LeanModularForms` project (Chris Birkbeck,
Apache-2.0, <https://github.com/CBirkbeck/AINTLIB> @ `2baa76f742bd`),
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

/-- **Every cusp form raised along `d * M ∣ N` from `S_k(Γ₁(M))` is a linear combination of
level-raised newforms of levels dividing `M`**: `∑_{d * M ∣ N} V_d S_k(Γ₁(M))` lies in the span of
`V_c g'` with `c * M' ∣ N` and `M' ∣ M`, refining `span_levelRaise_eq_top` by applying it at level
`M` and composing `V_d ∘ V_e = V_{e * d}`. -/
theorem iSup_range_levelRaise_le_span_levelRaise {M : ℕ} [NeZero N] [NeZero M] :
    (⨆ (d : ℕ) (hd : d * M ∣ N),
      haveI : NeZero d := NeZero.of_dvd (dvd_of_mul_right_dvd hd)
      LinearMap.range
        (CuspForm.levelRaiseₗ (k := k) d (Gamma1_map_le_conjAct_scaleGL_of_dvd hd))) ≤
    Submodule.span ℂ {G : CuspForm ((Gamma1 N).map (mapGL ℝ)) k |
      ∃ (M' c : ℕ) (_ : NeZero M') (_ : NeZero c) (hc : c * M' ∣ N),
        M' ∣ M ∧ ∃ g' : Newform M' k,
          CuspForm.levelRaise c (Gamma1_map_le_conjAct_scaleGL_of_dvd hc) g'.toCuspForm = G} := by
  refine iSup_le fun d ↦ iSup_le fun hd ↦ ?_
  have : NeZero d := NeZero.of_dvd (dvd_of_mul_right_dvd hd)
  rw [← Submodule.map_top, ← span_levelRaise_eq_top M k, Submodule.map_span, Submodule.span_le]
  rintro _ ⟨_, ⟨M', e, _, _, he, g', rfl⟩, rfl⟩
  have hed : (e * d) * M' ∣ N := by
    rw [mul_comm e d, mul_assoc]
    exact (mul_dvd_mul_left d he).trans hd
  have : NeZero (e * d) := ⟨mul_ne_zero (NeZero.ne e) (NeZero.ne d)⟩
  rw [CuspForm.levelRaiseₗ_apply, CuspForm.levelRaise_levelRaise]
  exact Submodule.subset_span ⟨M', e * d, inferInstance, inferInstance, hed,
    dvd_of_mul_left_dvd he, g', rfl⟩

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

/-- **A nonzero simultaneous eigenvector of the good Hecke operators in `S_k(N, χ)` has the
eigenvalues of a newform whose nebentypus induces `χ`.** If a nonzero `F ∈ S_k(N, χ)` satisfies
`Tₚ F = aₚ F` at every prime `p ∤ N`, then some newform `g` of some level `M ∣ N` has eigenvalue
`aₚ` at every prime `p ∤ N`, and the nebentypus of `g`, read at level `N`, is `χ`. This is the
existence half of Diamond–Shurman's Proposition 5.8.4 with the character stated. -/
theorem exists_newform_comp_unitsMap_eq_and_eigenvalue_eq_of_forall_heckeTCuspNat_eq_smul
    [NeZero N] {χ : (ZMod N)ˣ →* ℂˣ} {F : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hFχ : F ∈ cuspFormCharSpace k χ) (hF0 : F ≠ 0)
    {a : ∀ p : ℕ, p.Prime → Nat.Coprime p N → ℂ}
    (hF : ∀ (p : ℕ) (hp : p.Prime) (hpN : Nat.Coprime p N),
      heckeTCuspNat k p (_hn := ⟨hp.ne_zero⟩) F = a p hp hpN • F) :
    ∃ (M : ℕ) (_ : NeZero M) (hM : M ∣ N) (g : Newform M k),
      g.χ.comp (ZMod.unitsMap hM) = χ ∧
      ∀ (p : ℕ) (hp : p.Prime) (hpN : Nat.Coprime p N),
        g.eigenvalue ⟨p, hp.pos⟩ (hpN.coprime_dvd_right hM) = a p hp hpN := by
  by_contra hne
  -- otherwise every level-raised newform spanning `F` lies in a nebentypus space other than `χ`
  refine hF0 ((Submodule.disjoint_def.mp (iSupIndep_def.mp (iSupIndep_cuspFormCharSpace k) χ))
    F hFχ (Submodule.span_le.mpr ?_ (mem_span_levelRaise_of_forall_heckeTCuspNat_eq_smul hF)))
  rintro _ ⟨M, d, _, _, hdM, g, hg, rfl⟩
  have hgχ : g.χ.comp (ZMod.unitsMap (dvd_of_mul_left_dvd hdM)) ≠ χ :=
    fun h ↦ hne ⟨M, inferInstance, dvd_of_mul_left_dvd hdM, g, h, hg⟩
  exact Submodule.mem_iSup_of_mem _ (Submodule.mem_iSup_of_mem hgχ
    (CuspForm.levelRaise_mem_cuspFormCharSpace_of_dvd hdM g.χ g.mem_charSpace))

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

namespace HeckeRing.GL2.Newform

open TauCeti _root_.CuspForm

/-! ### Linear independence and bases of level-raised newforms -/

/-- **Linear independence of the level-raised newforms at a fixed nebentypus** (Diamond–Shurman,
Theorem 5.8.3). For a character `χ` modulo `N`, the level-raises `V_d g` over divisor levels
`M ∣ N`, newforms `g` of level `M` whose nebentypus pulls back to `χ`, and `d` with `d * M ∣ N` are
`ℂ`-linearly independent in `S_k(Γ₁(N))`. -/
theorem linearIndependent_levelRaise_of_comp_unitsMap_eq (N : ℕ) [NeZero N] (k : ℤ)
    (χ : (ZMod N)ˣ →* ℂˣ) :
    LinearIndependent ℂ
      (fun i : Σ M : {M : ℕ // M ∣ N},
          (letI : NeZero M.1 := NeZero.of_dvd M.2;
            {g : Newform M.1 k // g.χ.comp (ZMod.unitsMap M.2) = χ}) ×
            {d : ℕ // d * M.1 ∣ N} ↦
        letI : NeZero i.1.1 := NeZero.of_dvd i.1.2
        letI : NeZero i.2.2.1 := NeZero.of_dvd (dvd_of_mul_right_dvd i.2.2.2)
        CuspForm.levelRaise i.2.2.1 (Gamma1_map_le_conjAct_scaleGL_of_dvd i.2.2.2)
          i.2.1.1.toCuspForm) := by
  let P := {p : ℕ // p.Prime ∧ Nat.Coprime p N}
  let T : P → Module.End ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) := fun p ↦
    heckeTCuspNat k p.1 (_hn := ⟨p.2.1.ne_zero⟩)
  let η := Σ M : {M : ℕ // M ∣ N},
    letI : NeZero M.1 := NeZero.of_dvd M.2
    {g : Newform M.1 k // g.χ.comp (ZMod.unitsMap M.2) = χ}
  let fam : ∀ mg : η, {d : ℕ // d * mg.1.1 ∣ N} → CuspForm ((Gamma1 N).map (mapGL ℝ)) k :=
    fun mg d ↦
      letI : NeZero mg.1.1 := NeZero.of_dvd mg.1.2
      letI : NeZero d.1 := NeZero.of_dvd (dvd_of_mul_right_dvd d.2)
      CuspForm.levelRaise d.1 (Gamma1_map_le_conjAct_scaleGL_of_dvd d.2) mg.2.1.toCuspForm
  -- Step 1 (`_root_.CuspForm.linearIndependent_levelRaise`) gives independence of `V_d g` for each
  -- `(M, g)`; Step 2 (`eigenvalue_injective_of_comp_unitsMap_eq`) separates distinct `(M, g)` into
  -- independent joint `Tₚ`-eigenspaces (`p ∤ N`).
  have hli_sigma := TauCeti.linearIndependent_sigma_of_iSupIndep (f := fam)
    (fun mg ↦ by
      have : NeZero mg.1.1 := NeZero.of_dvd mg.1.2
      have : ∀ d : {d : ℕ // d * mg.1.1 ∣ N}, NeZero d.1 :=
        fun d ↦ NeZero.of_dvd (dvd_of_mul_right_dvd d.2)
      exact _root_.CuspForm.linearIndependent_levelRaise (one_mem_strictPeriods_Gamma1_map mg.1.1)
        mg.2.1.ne_zero Subtype.val_injective
        fun d ↦ Gamma1_map_le_conjAct_scaleGL_of_dvd d.2)
    ((iSupIndep_iInf_eigenspace T).comp (eigenvalue_injective_of_comp_unitsMap_eq N k χ))
    fun mg d ↦ by
      have : NeZero mg.1.1 := NeZero.of_dvd mg.1.2
      have : NeZero d.1 := NeZero.of_dvd (dvd_of_mul_right_dvd d.2)
      exact (Submodule.mem_iInf _).mpr fun p ↦ Module.End.mem_eigenspace_iff.mpr
        (mg.2.1.heckeTCuspNat_levelRaise_eq_eigenvalue_smul d.2 p.2.1 p.2.2)
  -- Reassociate `(M, (g, d))` with `((M, g), d)` to match the sigma-indexed family `fam`.
  let reindex :
      (Σ M : {M : ℕ // M ∣ N},
        (letI : NeZero M.1 := NeZero.of_dvd M.2;
          {g : Newform M.1 k // g.χ.comp (ZMod.unitsMap M.2) = χ}) ×
          {d : ℕ // d * M.1 ∣ N}) ≃
      Σ mg : η, {d : ℕ // d * mg.1.1 ∣ N} :=
    { toFun := fun i ↦ ⟨⟨i.1, i.2.1⟩, i.2.2⟩
      invFun := fun j ↦ ⟨j.1.1, j.1.2, j.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  exact hli_sigma.comp reindex reindex.injective

/-- **Linear independence of all level-raised newforms in `S_k(Γ₁(N))`** (Diamond–Shurman,
Theorem 5.8.3). As `M` ranges over the divisors of `N`, `g` over the newforms of level `M`, and `d`
over the positive divisors with `d * M ∣ N`, the cusp forms `V_d g` are `ℂ`-linearly independent. -/
theorem linearIndependent_levelRaise (N : ℕ) [NeZero N] (k : ℤ) :
    LinearIndependent ℂ
      (fun i : Σ M : {M : ℕ // M ∣ N},
          (letI : NeZero M.1 := NeZero.of_dvd M.2; Newform M.1 k) × {d : ℕ // d * M.1 ∣ N} ↦
        letI : NeZero i.1.1 := NeZero.of_dvd i.1.2
        letI : NeZero i.2.2.1 := NeZero.of_dvd (dvd_of_mul_right_dvd i.2.2.2)
        CuspForm.levelRaise i.2.2.1 (Gamma1_map_le_conjAct_scaleGL_of_dvd i.2.2.2)
          i.2.1.toCuspForm) := by
  -- Step 3: glue the fixed-character families across the independent subspaces `S_k(N, χ)`, then
  -- group each `(M, g, d)` under its lifted nebentypus `χ = g.χ ∘ unitsMap`.
  have hli_sigma := TauCeti.linearIndependent_sigma_of_iSupIndep
    (W := cuspFormCharSpace (N := N) k)
    (fun χ ↦ linearIndependent_levelRaise_of_comp_unitsMap_eq N k χ)
    (iSupIndep_cuspFormCharSpace k)
    fun χ i ↦ by
      have : NeZero i.1.1 := NeZero.of_dvd i.1.2
      have : NeZero i.2.2.1 := NeZero.of_dvd (dvd_of_mul_right_dvd i.2.2.2)
      have hmem := CuspForm.levelRaise_mem_cuspFormCharSpace_of_dvd i.2.2.2 i.2.1.1.χ
        i.2.1.1.mem_charSpace
      rwa [i.2.1.2] at hmem
  let reindex :
      (Σ M : {M : ℕ // M ∣ N},
        (letI : NeZero M.1 := NeZero.of_dvd M.2; Newform M.1 k) × {d : ℕ // d * M.1 ∣ N}) ≃
      Σ χ : (ZMod N)ˣ →* ℂˣ, Σ M : {M : ℕ // M ∣ N},
        (letI : NeZero M.1 := NeZero.of_dvd M.2;
          {g : Newform M.1 k // g.χ.comp (ZMod.unitsMap M.2) = χ}) ×
          {d : ℕ // d * M.1 ∣ N} :=
    { toFun := fun i ↦
        letI : NeZero i.1.1 := NeZero.of_dvd i.1.2
        ⟨i.2.1.χ.comp (ZMod.unitsMap i.1.2), i.1, ⟨i.2.1, rfl⟩, i.2.2⟩
      invFun := fun j ↦ ⟨j.2.1, j.2.2.1.1, j.2.2.2⟩
      left_inv := fun ⟨_, _, _⟩ ↦ rfl
      right_inv := fun ⟨_, _, ⟨_, rfl⟩, _⟩ ↦ rfl }
  exact hli_sigma.comp reindex reindex.injective

/-- **The level-raised newforms `V_d g` (`M ∣ N`, `d * M ∣ N`), as a `ℂ`-basis of `S_k(Γ₁(N))`**
(Diamond–Shurman, Theorem 5.8.3). -/
noncomputable def levelRaiseBasis (N : ℕ) [NeZero N] (k : ℤ) :
    Module.Basis
      (Σ M : {M : ℕ // M ∣ N},
        (letI : NeZero M.1 := NeZero.of_dvd M.2; Newform M.1 k) × {d : ℕ // d * M.1 ∣ N})
      ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :=
  Module.Basis.mk (linearIndependent_levelRaise N k) <| by
    refine (span_levelRaise_eq_top N k).ge.trans (Submodule.span_mono ?_)
    rintro _ ⟨M, d, _, _, h, g, rfl⟩
    exact ⟨⟨⟨M, dvd_of_mul_left_dvd h⟩, g, ⟨d, h⟩⟩, rfl⟩

/-- Evaluating `levelRaiseBasis` at `(M, g, d)` gives `V_d g`. -/
@[simp]
theorem levelRaiseBasis_apply (N : ℕ) [NeZero N] (k : ℤ)
    (i : Σ M : {M : ℕ // M ∣ N},
      (letI : NeZero M.1 := NeZero.of_dvd M.2; Newform M.1 k) × {d : ℕ // d * M.1 ∣ N}) :
    levelRaiseBasis N k i =
      (letI : NeZero i.1.1 := NeZero.of_dvd i.1.2;
        letI : NeZero i.2.2.1 := NeZero.of_dvd (dvd_of_mul_right_dvd i.2.2.2);
        CuspForm.levelRaise i.2.2.1 (Gamma1_map_le_conjAct_scaleGL_of_dvd i.2.2.2)
          i.2.1.toCuspForm) := by
  simp [levelRaiseBasis]

private noncomputable def levelRaiseToCharSpace (N : ℕ) [NeZero N] (k : ℤ)
    (χ : (ZMod N)ˣ →* ℂˣ)
    (i : Σ M : {M : ℕ // M ∣ N},
      (letI : NeZero M.1 := NeZero.of_dvd M.2;
        {g : Newform M.1 k // g.χ.comp (ZMod.unitsMap M.2) = χ}) ×
        {d : ℕ // d * M.1 ∣ N}) :
    cuspFormCharSpace k χ :=
  letI : NeZero i.1.1 := NeZero.of_dvd i.1.2
  letI : NeZero i.2.2.1 := NeZero.of_dvd (dvd_of_mul_right_dvd i.2.2.2)
  ⟨CuspForm.levelRaise i.2.2.1 (Gamma1_map_le_conjAct_scaleGL_of_dvd i.2.2.2) i.2.1.1.toCuspForm,
    by
      have hmem := CuspForm.levelRaise_mem_cuspFormCharSpace_of_dvd i.2.2.2 i.2.1.1.χ
        i.2.1.1.mem_charSpace
      rwa [i.2.1.2] at hmem⟩

private theorem linearIndependent_levelRaiseToCharSpace (N : ℕ) [NeZero N] (k : ℤ)
    (χ : (ZMod N)ˣ →* ℂˣ) :
    LinearIndependent ℂ (levelRaiseToCharSpace N k χ) :=
  LinearIndependent.of_comp (cuspFormCharSpace k χ).subtype
    (linearIndependent_levelRaise_of_comp_unitsMap_eq N k χ)

private theorem top_le_span_range_levelRaiseToCharSpace (N : ℕ) [NeZero N] (k : ℤ)
    (χ : (ZMod N)ˣ →* ℂˣ) :
    ⊤ ≤ Submodule.span ℂ (Set.range (levelRaiseToCharSpace N k χ)) := by
  rintro F -
  rw [← Submodule.comap_map_eq_of_injective (cuspFormCharSpace k χ).injective_subtype
    (Submodule.span ℂ _), Submodule.mem_comap]
  set S := (Submodule.span ℂ (Set.range (levelRaiseToCharSpace N k χ))).map
    (cuspFormCharSpace k χ).subtype
  set W := ⨆ (ψ : (ZMod N)ˣ →* ℂˣ) (_ : ψ ≠ χ), cuspFormCharSpace (N := N) k ψ
  have hSW : (F : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ∈ S ⊔ W := by
    refine Submodule.span_le.mpr ?_
      ((span_levelRaise_eq_top N k).ge (Submodule.mem_top (x := F.1)))
    rintro _ ⟨M, d, _, _, hdM, g, rfl⟩
    have hMN : M ∣ N := dvd_of_mul_left_dvd hdM
    by_cases hgχ : g.χ.comp (ZMod.unitsMap hMN) = χ
    · exact Submodule.mem_sup_left (Submodule.mem_map.mpr
        ⟨levelRaiseToCharSpace N k χ ⟨⟨M, hMN⟩, ⟨g, hgχ⟩, ⟨d, hdM⟩⟩,
          Submodule.subset_span (Set.mem_range_self _), rfl⟩)
    · exact Submodule.mem_sup_right (Submodule.mem_iSup_of_mem _ (Submodule.mem_iSup_of_mem hgχ
        (CuspForm.levelRaise_mem_cuspFormCharSpace_of_dvd hdM g.χ g.mem_charSpace)))
  obtain ⟨s, hs, t, ht, hst⟩ := Submodule.mem_sup.mp hSW
  have hsχ : s ∈ cuspFormCharSpace k χ :=
    Submodule.map_subtype_le (cuspFormCharSpace k χ) _ hs
  have htχ : t ∈ cuspFormCharSpace k χ := by
    have hsub := Submodule.sub_mem _ F.2 hsχ
    rwa [← hst, add_sub_cancel_left] at hsub
  have ht0 : t = 0 :=
    (Submodule.disjoint_def.mp (iSupIndep_def.mp (iSupIndep_cuspFormCharSpace k) χ)) t htχ ht
  rw [ht0, add_zero] at hst
  rw [Submodule.coe_subtype, ← hst]
  exact hs

/-- **The level-raised newforms whose nebentypus pulls back to `χ`, as a `ℂ`-basis of
`S_k(N, χ)`** (Diamond–Shurman, Theorem 5.8.3). -/
noncomputable def levelRaiseBasisCharSpace (N : ℕ) [NeZero N] (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) :
    Module.Basis
      (Σ M : {M : ℕ // M ∣ N},
        (letI : NeZero M.1 := NeZero.of_dvd M.2;
          {g : Newform M.1 k // g.χ.comp (ZMod.unitsMap M.2) = χ}) ×
          {d : ℕ // d * M.1 ∣ N})
      ℂ (cuspFormCharSpace k χ) :=
  Module.Basis.mk
    (linearIndependent_levelRaiseToCharSpace N k χ)
    (top_le_span_range_levelRaiseToCharSpace N k χ)

/-- Evaluating `levelRaiseBasisCharSpace` at `(M, g, d)` gives `V_d g` inside `S_k(N, χ)`. -/
@[simp]
theorem coe_levelRaiseBasisCharSpace_apply (N : ℕ) [NeZero N] (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (i : Σ M : {M : ℕ // M ∣ N},
      (letI : NeZero M.1 := NeZero.of_dvd M.2;
        {g : Newform M.1 k // g.χ.comp (ZMod.unitsMap M.2) = χ}) ×
        {d : ℕ // d * M.1 ∣ N}) :
    (levelRaiseBasisCharSpace N k χ i : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) =
      (letI : NeZero i.1.1 := NeZero.of_dvd i.1.2;
        letI : NeZero i.2.2.1 := NeZero.of_dvd (dvd_of_mul_right_dvd i.2.2.2);
        CuspForm.levelRaise i.2.2.1 (Gamma1_map_le_conjAct_scaleGL_of_dvd i.2.2.2)
          i.2.1.1.toCuspForm) := by
  simp [levelRaiseBasisCharSpace, levelRaiseToCharSpace]

end HeckeRing.GL2.Newform

namespace TauCeti

open _root_.CuspForm HeckeRing.GL2

/-! ### Internal direct-sum decompositions of `S_k(Γ₁(N))` and `S_k(N, χ)` -/

/-- **The level-raised newspaces `V_d S_k(Γ₁(M))ⁿᵉʷ` (`d * M ∣ N`) span `S_k(Γ₁(N))`**
(Diamond–Shurman, Theorem 5.8.3). -/
theorem iSup_map_levelRaiseₗ_cuspFormsNew_eq_top (N : ℕ) [NeZero N] (k : ℤ) :
    (⨆ md : {md : ℕ × ℕ // md.2 * md.1 ∣ N},
      letI : NeZero md.1.1 := NeZero.of_dvd (dvd_of_mul_left_dvd md.2)
      letI : NeZero md.1.2 := NeZero.of_dvd (dvd_of_mul_right_dvd md.2)
      (cuspFormsNew md.1.1 k).map
        (CuspForm.levelRaiseₗ md.1.2 (Gamma1_map_le_conjAct_scaleGL_of_dvd md.2))) = ⊤ := by
  refine eq_top_iff.mpr ((Newform.span_levelRaise_eq_top N k).ge.trans (Submodule.span_le.mpr ?_))
  rintro _ ⟨M, d, _, _, h, g, rfl⟩
  exact Submodule.mem_iSup_of_mem ⟨(M, d), h⟩ ⟨g.toCuspForm, g.isNew, CuspForm.levelRaiseₗ_apply ..⟩

/-- **The level-raised newspaces `V_d S_k(Γ₁(M))ⁿᵉʷ` (`d * M ∣ N`) are linearly independent**
(Diamond–Shurman, Theorem 5.8.3). -/
theorem iSupIndep_map_levelRaiseₗ_cuspFormsNew (N : ℕ) [NeZero N] (k : ℤ) :
    iSupIndep (fun md : {md : ℕ × ℕ // md.2 * md.1 ∣ N} ↦
      letI : NeZero md.1.1 := NeZero.of_dvd (dvd_of_mul_left_dvd md.2)
      letI : NeZero md.1.2 := NeZero.of_dvd (dvd_of_mul_right_dvd md.2)
      (cuspFormsNew md.1.1 k).map
        (CuspForm.levelRaiseₗ md.1.2 (Gamma1_map_le_conjAct_scaleGL_of_dvd md.2))) := by
  let π : (Σ M : {M : ℕ // M ∣ N},
      (letI : NeZero M.1 := NeZero.of_dvd M.2; Newform M.1 k) × {d : ℕ // d * M.1 ∣ N}) →
      {md : ℕ × ℕ // md.2 * md.1 ∣ N} :=
    fun i ↦ ⟨(i.1.1, i.2.2.1), i.2.2.2⟩
  refine ((Newform.levelRaiseBasis N k).isInternal_span_image_fiber π).submodule_iSupIndep.mono
    fun md ↦ ?_
  have : NeZero md.1.1 := NeZero.of_dvd (dvd_of_mul_left_dvd md.2)
  have : NeZero md.1.2 := NeZero.of_dvd (dvd_of_mul_right_dvd md.2)
  rw [← Newform.span_range_toCuspForm_eq_cuspFormsNew, Submodule.map_span, Submodule.span_le]
  rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
  refine Submodule.subset_span
    ⟨⟨⟨md.1.1, dvd_of_mul_left_dvd md.2⟩, g, ⟨md.1.2, md.2⟩⟩, Subtype.ext rfl, ?_⟩
  simp [CuspForm.levelRaiseₗ_apply]

/-- **Internal direct-sum decomposition of `S_k(Γ₁(N))`** into the level-raised newspaces
`V_d S_k(Γ₁(M))ⁿᵉʷ` over all pairs `(M, d)` with `d * M ∣ N` (Diamond–Shurman, Theorem 5.8.3). -/
theorem isInternal_map_levelRaiseₗ_cuspFormsNew (N : ℕ) [NeZero N] (k : ℤ) :
    DirectSum.IsInternal (fun md : {md : ℕ × ℕ // md.2 * md.1 ∣ N} ↦
      letI : NeZero md.1.1 := NeZero.of_dvd (dvd_of_mul_left_dvd md.2)
      letI : NeZero md.1.2 := NeZero.of_dvd (dvd_of_mul_right_dvd md.2)
      (cuspFormsNew md.1.1 k).map
        (CuspForm.levelRaiseₗ md.1.2 (Gamma1_map_le_conjAct_scaleGL_of_dvd md.2))) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (iSupIndep_map_levelRaiseₗ_cuspFormsNew N k)
    (iSup_map_levelRaiseₗ_cuspFormsNew_eq_top N k)

/-- **The level-raised character newspaces `V_d S_k(M, χ_M)ⁿᵉʷ` (`d * M ∣ N`, `cond χ ∣ M`) span
`S_k(N, χ)`** (Diamond–Shurman, Theorem 5.8.3). -/
theorem iSup_map_levelRaiseₗ_cuspFormsNew_inf_cuspFormCharSpace_eq_cuspFormCharSpace (N : ℕ)
    [NeZero N] (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) :
    (⨆ md : {md : ℕ × ℕ //
        md.2 * md.1 ∣ N ∧ DirichletCharacter.conductor (MulChar.ofUnitHom χ) ∣ md.1},
      letI : NeZero md.1.1 := NeZero.of_dvd (dvd_of_mul_left_dvd md.2.1)
      letI : NeZero md.1.2 := NeZero.of_dvd (dvd_of_mul_right_dvd md.2.1)
      (cuspFormsNew md.1.1 k ⊓ cuspFormCharSpace k
        ((DirichletCharacter.primitiveCharacter (MulChar.ofUnitHom χ)).toUnitHom.comp
          (ZMod.unitsMap md.2.2))).map
        (CuspForm.levelRaiseₗ md.1.2 (Gamma1_map_le_conjAct_scaleGL_of_dvd md.2.1))) =
      cuspFormCharSpace k χ := by
  refine le_antisymm (iSup_le fun md ↦ ?_) fun F hF ↦ ?_
  · have : NeZero md.1.1 := NeZero.of_dvd (dvd_of_mul_left_dvd md.2.1)
    have : NeZero md.1.2 := NeZero.of_dvd (dvd_of_mul_right_dvd md.2.1)
    rintro _ ⟨g, hg, rfl⟩
    rw [CuspForm.levelRaiseₗ_apply]
    have hmem := CuspForm.levelRaise_mem_cuspFormCharSpace_of_dvd md.2.1 _ hg.2
    rwa [MonoidHom.comp_assoc, ZMod.unitsMap_comp,
      DirichletCharacter.primitiveCharacter_toUnitHom_comp_unitsMap] at hmem
  · have hbasis : (⟨F, hF⟩ : cuspFormCharSpace k χ) ∈
        Submodule.span ℂ (Set.range (Newform.levelRaiseBasisCharSpace N k χ)) := by
      rw [(Newform.levelRaiseBasisCharSpace N k χ).span_eq]
      exact Submodule.mem_top
    have hmap := Submodule.mem_map_of_mem (f := (cuspFormCharSpace k χ).subtype) hbasis
    rw [Submodule.map_span, ← Set.range_comp] at hmap
    refine Submodule.span_le.mpr (Set.range_subset_iff.mpr ?_) hmap
    intro i
    have : NeZero i.1.1 := NeZero.of_dvd i.1.2
    have : NeZero i.2.2.1 := NeZero.of_dvd (dvd_of_mul_right_dvd i.2.2.2)
    have hcM : DirichletCharacter.conductor (MulChar.ofUnitHom χ) ∣ i.1.1 :=
      DirichletCharacter.conductor_ofUnitHom_dvd_of_comp_unitsMap_eq i.1.2 i.2.1.2
    have hgχ : i.2.1.1.χ =
        (DirichletCharacter.primitiveCharacter (MulChar.ofUnitHom χ)).toUnitHom.comp
          (ZMod.unitsMap hcM) :=
      (ZMod.comp_unitsMap_eq_iff hcM i.1.2 _).mp
        (i.2.1.2.trans (DirichletCharacter.primitiveCharacter_toUnitHom_comp_unitsMap χ).symm)
    refine Submodule.mem_iSup_of_mem ⟨(i.1.1, i.2.2.1), i.2.2.2, hcM⟩
      ⟨i.2.1.1.toCuspForm, ⟨i.2.1.1.isNew, hgχ ▸ i.2.1.1.mem_charSpace⟩, ?_⟩
    simp [CuspForm.levelRaiseₗ_apply]

/-- **The level-raised character newspaces `V_d S_k(M, χ_M)ⁿᵉʷ` (`d * M ∣ N`, `cond χ ∣ M`) are
linearly independent** (Diamond–Shurman, Theorem 5.8.3). -/
theorem iSupIndep_map_levelRaiseₗ_cuspFormsNew_inf_cuspFormCharSpace (N : ℕ) [NeZero N] (k : ℤ)
    (χ : (ZMod N)ˣ →* ℂˣ) :
    iSupIndep (fun md : {md : ℕ × ℕ //
        md.2 * md.1 ∣ N ∧ DirichletCharacter.conductor (MulChar.ofUnitHom χ) ∣ md.1} ↦
      letI : NeZero md.1.1 := NeZero.of_dvd (dvd_of_mul_left_dvd md.2.1)
      letI : NeZero md.1.2 := NeZero.of_dvd (dvd_of_mul_right_dvd md.2.1)
      (cuspFormsNew md.1.1 k ⊓ cuspFormCharSpace k
        ((DirichletCharacter.primitiveCharacter (MulChar.ofUnitHom χ)).toUnitHom.comp
          (ZMod.unitsMap md.2.2))).map
        (CuspForm.levelRaiseₗ md.1.2 (Gamma1_map_le_conjAct_scaleGL_of_dvd md.2.1))) := by
  have hinj : Function.Injective
      (fun md : {md : ℕ × ℕ //
          md.2 * md.1 ∣ N ∧ DirichletCharacter.conductor (MulChar.ofUnitHom χ) ∣ md.1} ↦
        (⟨md.1, md.2.1⟩ : {md : ℕ × ℕ // md.2 * md.1 ∣ N})) :=
    fun _ _ h ↦ Subtype.ext (Subtype.mk.inj h)
  exact ((iSupIndep_map_levelRaiseₗ_cuspFormsNew N k).comp hinj).mono
    fun _ ↦ Submodule.map_mono inf_le_left

/-- **Internal direct-sum decomposition of `S_k(N, χ)`** into the level-raised character newspaces
`V_d S_k(M, χ_M)ⁿᵉʷ` over all pairs `(M, d)` with `d * M ∣ N` and `cond χ ∣ M` (Diamond–Shurman,
Theorem 5.8.3). -/
theorem isInternal_comap_map_levelRaiseₗ_cuspFormsNew_inf_cuspFormCharSpace (N : ℕ) [NeZero N]
    (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) :
    DirectSum.IsInternal (fun md : {md : ℕ × ℕ //
        md.2 * md.1 ∣ N ∧ DirichletCharacter.conductor (MulChar.ofUnitHom χ) ∣ md.1} ↦
      letI : NeZero md.1.1 := NeZero.of_dvd (dvd_of_mul_left_dvd md.2.1)
      letI : NeZero md.1.2 := NeZero.of_dvd (dvd_of_mul_right_dvd md.2.1)
      ((cuspFormsNew md.1.1 k ⊓ cuspFormCharSpace k
        ((DirichletCharacter.primitiveCharacter (MulChar.ofUnitHom χ)).toUnitHom.comp
          (ZMod.unitsMap md.2.2))).map
        (CuspForm.levelRaiseₗ md.1.2 (Gamma1_map_le_conjAct_scaleGL_of_dvd md.2.1))).comap
        (cuspFormCharSpace k χ).subtype) :=
  DirectSum.isInternal_comap_subtype_of_iSupIndep_of_iSup_eq
    (iSupIndep_map_levelRaiseₗ_cuspFormsNew_inf_cuspFormCharSpace N k χ)
    (iSup_map_levelRaiseₗ_cuspFormsNew_inf_cuspFormCharSpace_eq_cuspFormCharSpace N k χ)

end TauCeti

