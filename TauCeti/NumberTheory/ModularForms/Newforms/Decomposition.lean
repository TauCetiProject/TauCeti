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

## Main results

* `HeckeRing.GL2.Newform.span_levelRaise_eq_top`: the level-raised newforms span `S_k(Γ₁(N))`.
* `HeckeRing.GL2.Newform.mem_span_levelRaise_of_forall_heckeTCuspNat_eq_smul`: a simultaneous
  eigenvector of the good `Tₚ` lies in the span of the level-raised newforms with its
  eigenvalues.
* `HeckeRing.GL2.Newform.exists_newform_eigenvalue_eq_of_forall_heckeTCuspNat_eq_smul` and
  `HeckeRing.GL2.EigenformAwayFromLevel.exists_newform_eigenvalue_eq`: a nonzero simultaneous
  eigenvector of the good `Tₚ`, in particular a good Hecke eigenform, shares its eigenvalues at
  the primes not dividing the level with a newform of divisor level.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005],
  Theorem 5.8.3 and Proposition 5.8.4.
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
    have hV : CuspForm.levelRaise 1 (Gamma1_map_le_conjAct_scaleGL_of_dvd h) f = f :=
      _root_.CuspForm.ext fun τ ↦ by simp
    rwa [CuspForm.levelRaiseₗ_apply, hV] at hf'

/-- **A simultaneous eigenvector of the good Hecke operators lies in the span of the level-raised
newforms with its eigenvalues.** If a cusp form `F` of level `Γ₁(N)` satisfies `Tₚ F = aₚ F` at
every prime `p ∤ N`, then `F` is a combination of forms `V_d g`, `d * M ∣ N`, with `g` a newform
of level `M` whose eigenvalue at every prime `p ∤ N` is `aₚ`. -/
theorem mem_span_levelRaise_of_forall_heckeTCuspNat_eq_smul [NeZero N]
    {F : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} {a : ℕ → ℂ}
    (hF : ∀ (p : ℕ) (hp : p.Prime), Nat.Coprime p N →
      heckeTCuspNat k p (_hn := ⟨hp.ne_zero⟩) F = a p • F) :
    F ∈ Submodule.span ℂ {G : CuspForm ((Gamma1 N).map (mapGL ℝ)) k |
      ∃ (M d : ℕ) (_ : NeZero M) (_ : NeZero d) (h : d * M ∣ N) (g : Newform M k),
        (∀ (p : ℕ) (hp : p.Prime) (hpN : Nat.Coprime p N),
          g.eigenvalue ⟨p, hp.pos⟩ (hpN.coprime_dvd_right (dvd_of_mul_left_dvd h)) = a p) ∧
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
    rw [heckeTCuspNat_levelRaise k h p.2.1 p.2.2,
      g.heckeTCuspNat_eq_eigenvalue_smul p.2.1 (p.2.2.coprime_dvd_right (dvd_of_mul_left_dvd h)),
      hg p, ← CuspForm.levelRaiseₗ_apply, map_smul, CuspForm.levelRaiseₗ_apply]
  -- the spaces `S χ` together span everything
  have htop : ⨆ χ, S χ = ⊤ := by
    refine eq_top_iff.mpr ((span_levelRaise_eq_top N k).ge.trans (Submodule.span_le.mpr ?_))
    rintro _ ⟨M, d, _, _, h, g, rfl⟩
    exact Submodule.mem_iSup_of_mem (fun p : ι ↦ g.eigenvalue ⟨p.1, p.2.1.pos⟩
      (p.2.2.coprime_dvd_right (dvd_of_mul_left_dvd h)))
      (Submodule.subset_span ⟨M, d, inferInstance, inferInstance, h, g, fun _ ↦ rfl, rfl⟩)
  -- split off the component of `F` with the eigenvalues `a`; the rest is an eigenvector for `a`
  -- lying in the span of the other joint eigenspaces, hence zero
  let a' : ι → ℂ := fun p ↦ a p
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
    {F : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hF0 : F ≠ 0) {a : ℕ → ℂ}
    (hF : ∀ (p : ℕ) (hp : p.Prime), Nat.Coprime p N →
      heckeTCuspNat k p (_hn := ⟨hp.ne_zero⟩) F = a p • F) :
    ∃ (M : ℕ) (_ : NeZero M) (hM : M ∣ N) (g : Newform M k),
      ∀ (p : ℕ) (hp : p.Prime) (hpN : Nat.Coprime p N),
        g.eigenvalue ⟨p, hp.pos⟩ (hpN.coprime_dvd_right hM) = a p := by
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
        g.eigenvalue ⟨p, hp.pos⟩ (hpN.coprime_dvd_right hM) = f.eigenvalue ⟨p, hp.pos⟩ hpN := by
  classical
  -- the eigenvalues of `f`, extended by `0` to the indices where they are not defined
  obtain ⟨M, _, hM, g, hg⟩ := Newform.exists_newform_eigenvalue_eq_of_forall_heckeTCuspNat_eq_smul
    f.ne_zero (a := fun p ↦
      if hp : p.Prime ∧ Nat.Coprime p N then f.eigenvalue ⟨p, hp.1.pos⟩ hp.2 else 0)
    fun p hp hpN ↦ by rw [f.heckeTCuspNat_eq_eigenvalue_smul hp hpN, dite_eq_left ⟨hp, hpN⟩]
  exact ⟨M, inferInstance, hM, g, fun p hp hpN ↦ by rw [hg p hp hpN, dite_eq_left ⟨hp, hpN⟩]⟩

end HeckeRing.GL2
