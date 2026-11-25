/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.PrimaryComponent
public import Mathlib.Algebra.MvPolynomial.Variables
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.SupportedKernel
public import TauCeti.AlgebraicGeometry.Modules.Tilde.Basic

/-!
# A witness outside the quasi-compact regime of strict transforms

Let `k` be a field, `A = k[x_0, x_1, …]`, `I = (x_0, x_1, …)`, `B = A/(x_j^{j+2} : j ≥ 0)`,
`S = Spec A` and `U = S ∖ V(I)`, the union of the basic opens `D(x_j)`. Then:

* `U` is dense in the integral scheme `S`, a witness for the identity modification (`dense_U`), but
  the inclusion `U ⟶ S` is not quasi-compact (`not_quasiCompact_ι`): finitely many `D(x_j)` with
  `j ≤ N` miss the prime `(x_0, …, x_N)`, which lies in `D(x_{N+1})`.
* Every section of `B~` vanishes on `U`, since `x_j^{j+2}` kills `B` and some `x_j` is invertible
  at each point of `U`: the supported kernel of `B~` along `U` is all of `B~`
  (`mem_range_supportedKernelι_app`), so the quotient by it is zero.
* `B` has no `I`-power torsion (`primaryComponent_eq_bot`): for a class `b ≠ 0` and any `n`, a
  variable `x_j` not occurring in a representative of `b`, with `j + 2 > n`, has `x_j^n b ≠ 0`.

So the support-defined quotient (`AlgebraicGeometry.Scheme.Modules.supportedQuotient`) and the
`I`-power-torsion quotient of `B~` differ for this witness: their comparison
(`AlgebraicGeometry.Scheme.Modules.mem_range_supportedKernelι_app_iff_mem_primaryComponent`) needs a
quasi-compact open.
-/

public section

noncomputable section

open MvPolynomial AlgebraicGeometry

namespace TauCeti.StrictTransformNonQuasiCompactExample

universe u
variable (k : Type u) [Field k]

/-- The ideal `(x_j^{j+2} : j ≥ 0)` of `k[x_0, x_1, …]`. -/
noncomputable abbrev J : Ideal (MvPolynomial ℕ k) :=
  Ideal.span ((fun s ↦ monomial s (1 : k)) '' Set.range fun j : ℕ ↦ Finsupp.single j (j + 2))

/-- The ideal `I = (x_0, x_1, …)`. -/
noncomputable abbrev I : Ideal (MvPolynomial ℕ k) := Ideal.span (Set.range X)

/-- `B = k[x_0, x_1, …]/(x_j^{j+2} : j ≥ 0)`. -/
abbrev B : Type u := MvPolynomial ℕ k ⧸ J k

/-- If `p ∉ (x_j^{j+2} : j ≥ 0)`, then for every `n` some `x_j^n p` is still outside: take `j`
larger than `n` and than every variable of `p`. -/
theorem X_pow_mul_notMem {p : MvPolynomial ℕ k} (hp : p ∉ J k) (n : ℕ) :
    ∃ j, X j ^ n * p ∉ J k := by
  rw [mem_ideal_span_monomial_image] at hp
  push Not at hp
  obtain ⟨m, hm, hm'⟩ := hp
  refine ⟨p.vars.sup id + n + 1, fun h ↦ ?_⟩
  set j := p.vars.sup id + n + 1
  have hj : m j = 0 := by
    by_contra h0
    have : j ∈ p.vars := (mem_vars_iff_mem_support j).2 ⟨m, hm, Finsupp.mem_support_iff.2 h0⟩
    have := Finset.le_sup (f := id) this
    simp only [id] at this
    omega
  rw [X_pow_eq_monomial, mem_ideal_span_monomial_image] at h
  obtain ⟨_, ⟨j', rfl⟩, hle⟩ := h (Finsupp.single j n + m) (by
    rw [mem_support_iff, coeff_monomial_mul, one_mul]
    exact mem_support_iff.1 hm)
  rw [Finsupp.single_le_iff] at hle
  by_cases hjj : j' = j
  · subst hjj
    simp [hj] at hle
    omega
  · refine hm' _ ⟨j', rfl⟩ ?_
    rw [Finsupp.single_le_iff]
    simpa [Finsupp.single_apply, Ne.symm hjj] using hle

/-- **`B` has no `I`-power torsion.** -/
theorem primaryComponent_eq_bot : (I k).primaryComponent (B k) = ⊥ := by
  refine eq_bot_iff.2 fun b hb ↦ ?_
  obtain ⟨n, hn⟩ := (Ideal.primaryComponent_mem _ _ b).1 hb
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective b
  rw [Submodule.mem_bot, Ideal.Quotient.eq_zero_iff_mem]
  by_contra hp
  obtain ⟨j, hj⟩ := X_pow_mul_notMem k hp n
  have hX : X j ^ n ∈ I k ^ n := Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self j)) n
  have h := (Submodule.mem_torsionBySet_iff _ _).1 hn ⟨_, hX⟩
  apply hj
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul]
  exact h

/-- `B` as a module over `A = k[x_0, x_1, …]`. -/
noncomputable abbrev Bmod : ModuleCat.{u} (CommRingCat.of (MvPolynomial ℕ k)) :=
  ModuleCat.of _ (B k)

/-- The open `U = Spec A ∖ V(I)`, the union of the basic opens `D(x_j)`. -/
noncomputable abbrev U : (Spec (CommRingCat.of (MvPolynomial ℕ k))).Opens :=
  ⨆ j : ℕ, PrimeSpectrum.basicOpen (X j : MvPolynomial ℕ k)

/-- `U` is dense in the integral scheme `Spec A`, so it is a witness for the identity
modification. -/
theorem dense_U : Dense (U k : Set (Spec (CommRingCat.of (MvPolynomial ℕ k)))) := by
  refine (U k).isOpen.dense ⟨⟨⊥, Ideal.isPrime_bot⟩, TopologicalSpace.Opens.mem_iSup.2 ⟨0,
    (PrimeSpectrum.mem_basicOpen _ _).2 ?_⟩⟩
  simp [X_ne_zero]

/-- `x_j^{j+2}` kills `B`. -/
theorem X_pow_smul (j : ℕ) (b : Bmod k) : (X j ^ (j + 2) : MvPolynomial ℕ k) • b = 0 := by
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective (b : B k)
  change Ideal.Quotient.mk _ _ * Ideal.Quotient.mk _ q = 0
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, X_pow_eq_monomial]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨_, ⟨j, rfl⟩, rfl⟩)

/-- The sections of `B~` over any open inside `U` vanish. -/
theorem subsingleton_tilde_of_le {W : (Spec (CommRingCat.of (MvPolynomial ℕ k))).Opens}
    (hW : W ≤ U k) : Subsingleton Γ(tilde (Bmod k), W) := by
  refine ⟨fun s t ↦ Subtype.ext (funext fun p ↦ ?_)⟩
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 (hW p.property)
  have : Subsingleton (LocalizedModule p.val.asIdeal.primeCompl (Bmod k)) :=
    (IsLocalizedModule.subsingleton_iff p.val.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap _ _)).2 fun m ↦
        ⟨X j ^ (j + 2), fun h ↦ (PrimeSpectrum.mem_basicOpen _ _).1 hj
          (p.val.isPrime.mem_of_pow_mem _ h), X_pow_smul k j m⟩
  exact Subsingleton.elim _ _

/-- **The supported kernel of `B~` along `U` is everything**: every section of `B~` vanishes on
`U`. -/
theorem mem_range_supportedKernelι_app {W : (Spec (CommRingCat.of (MvPolynomial ℕ k))).Opens}
    (s : Γ(tilde (Bmod k), W)) :
    s ∈ Set.range (((tilde (Bmod k)).supportedKernelι (U k).ι).app W) := by
  rw [Scheme.Modules.mem_range_supportedKernelι_app_iff]
  have := subsingleton_tilde_of_le k (W := (U k).ι ''ᵁ ((U k).ι ⁻¹ᵁ W))
    ((Scheme.Hom.image_le_opensRange _ _).trans (by simp))
  exact Subsingleton.elim _ _

/-- **The inclusion of `U` is not quasi-compact**: finitely many `D(x_j)`, `j ≤ N`, miss the prime
`(x_0, …, x_N)` of `U`. -/
theorem not_quasiCompact_ι : ¬ QuasiCompact (U k).ι := by
  intro h
  have hc : IsCompact (U k : Set (Spec (CommRingCat.of (MvPolynomial ℕ k)))) := by
    have := (h.isCompact_preimage _ isOpen_univ isCompact_univ).image (U k).ι.continuous
    rwa [Set.preimage_univ, Set.image_univ, Scheme.Opens.range_ι] at this
  obtain ⟨t, ht⟩ := hc.elim_finite_subcover
    (fun j ↦ SetLike.coe (PrimeSpectrum.basicOpen (X j : MvPolynomial ℕ k) :
      (Spec (CommRingCat.of (MvPolynomial ℕ k))).Opens))
    (fun j ↦ (PrimeSpectrum.basicOpen _).isOpen) (by
      intro p hp
      obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hp
      refine Set.mem_iUnion.2 ⟨j, ?_⟩
      exact hj)
  set N := t.sup id
  let φ : MvPolynomial ℕ k →ₐ[k] MvPolynomial ℕ k := aeval fun i ↦ if i ≤ N then 0 else X i
  let q : PrimeSpectrum (MvPolynomial ℕ k) := ⟨RingHom.ker φ, RingHom.ker_isPrime _⟩
  have hq : q ∈ U k := TopologicalSpace.Opens.mem_iSup.2 ⟨N + 1, by
    rw [PrimeSpectrum.mem_basicOpen]
    change φ (X (N + 1)) ≠ 0
    simp [φ, X_ne_zero]⟩
  obtain ⟨j, hjt, hj⟩ := Set.mem_iUnion₂.1 (ht hq)
  apply (PrimeSpectrum.mem_basicOpen _ _).1 hj
  change φ (X j) = 0
  have hjN : j ≤ N := Finset.le_sup (f := id) hjt
  simp [φ, hjN]

end TauCeti.StrictTransformNonQuasiCompactExample
