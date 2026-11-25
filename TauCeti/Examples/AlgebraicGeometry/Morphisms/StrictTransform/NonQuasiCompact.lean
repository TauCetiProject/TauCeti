/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.PrimaryComponent
public import Mathlib.Algebra.MvPolynomial.Variables
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.SupportedKernel.Basic
public import TauCeti.AlgebraicGeometry.Modules.Tilde.Basic

/-!
# A witness outside the quasi-compact regime of strict transforms

Let `k` be a commutative ring, `A = k[x_0, x_1, …]`, `I = (x_0, x_1, …)`,
`B = A/(x_j^{j+2} : j ≥ 0)`, `S = Spec A` and `U = S ∖ V(I)`, the union of the basic opens
`D(x_j)`. Then:

* `U` is dense in `S`, a witness for the identity modification (`dense_U`), since `x_0` is a
  non-zero-divisor; but for `k ≠ 0` the inclusion `U ⟶ S` is not quasi-compact
  (`not_quasiCompact_ι`): finitely many `D(x_j)` with `j ≤ N` miss a prime containing
  `x_0, …, x_N`, which lies in `D(x_{N+1})`.
* Every section of `B~` vanishes on `U`, since `x_j^{j+2}` kills `B` and some `x_j` is invertible
  at each point of `U`: every section of `B~` lies in the supported kernel of `B~` along `U`
  (`mem_range_supportedKernelι_app`).
* `B` has no `I`-power torsion (`primaryComponent_eq_bot`): for a class `b ≠ 0` and any `n`, a
  variable `x_j` not occurring in a representative of `b`, with `j + 2 > n`, has `x_j^n b ≠ 0`.

So membership in the supported kernel along `U` is not membership in the `I`-power torsion for
this witness: their comparison
(`AlgebraicGeometry.Scheme.Modules.mem_range_supportedKernelι_app_iff_mem_primaryComponent`) needs a
quasi-compact open.
-/

public section

noncomputable section

open MvPolynomial AlgebraicGeometry

namespace TauCeti.StrictTransformNonQuasiCompactExample

universe u

section CommSemiring

variable (k : Type u) [CommSemiring k]

/-- The ideal `(x_j^{j+2} : j ≥ 0)` of `k[x_0, x_1, …]`. -/
noncomputable abbrev J : Ideal (MvPolynomial ℕ k) :=
  Ideal.span ((fun s ↦ monomial s (1 : k)) '' Set.range fun j : ℕ ↦ Finsupp.single j (j + 2))

/-- The ideal `I = (x_0, x_1, …)`. -/
noncomputable abbrev I : Ideal (MvPolynomial ℕ k) := Ideal.span (Set.range X)

/-- If `p ∉ (x_j^{j+2} : j ≥ 0)`, then for every `n` some `x_j^n p` is still outside. -/
private theorem X_pow_mul_notMem {p : MvPolynomial ℕ k} (hp : p ∉ J k) (n : ℕ) :
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
    simp only [Finsupp.add_apply, Finsupp.single_eq_same, hj, add_zero] at hle
    omega
  · refine hm' _ ⟨j', rfl⟩ ?_
    rw [Finsupp.single_le_iff]
    simpa [Finsupp.single_apply, Ne.symm hjj] using hle

end CommSemiring

variable (k : Type u) [CommRing k]

/-- `B = k[x_0, x_1, …]/(x_j^{j+2} : j ≥ 0)`. -/
abbrev B : Type u := MvPolynomial ℕ k ⧸ J k

/-- The `k[x_0, x_1, …]`-action on `B` is multiplication of representatives. -/
private theorem smul_mk (a q : MvPolynomial ℕ k) :
    a • (Ideal.Quotient.mk (J k) q : B k) = Ideal.Quotient.mk (J k) (a * q) := by
  rw [← Ideal.Quotient.mk_eq_mk, ← Submodule.Quotient.mk_smul, smul_eq_mul,
    Ideal.Quotient.mk_eq_mk]

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
  rw [smul_mk, Ideal.Quotient.eq_zero_iff_mem] at h
  exact hj h

/-- `B` as a module over `A = k[x_0, x_1, …]`. -/
noncomputable abbrev Bmod : ModuleCat.{u} (CommRingCat.of (MvPolynomial ℕ k)) :=
  ModuleCat.of _ (B k)

/-- The open `U = Spec A ∖ V(I)`, the union of the basic opens `D(x_j)`. -/
noncomputable abbrev U : (Spec (CommRingCat.of (MvPolynomial ℕ k))).Opens :=
  ⨆ j : ℕ, PrimeSpectrum.basicOpen (X j : MvPolynomial ℕ k)

/-- `U` is dense in `Spec A`, so it is a witness for the identity modification. -/
theorem dense_U : Dense (U k : Set (Spec (CommRingCat.of (MvPolynomial ℕ k)))) := by
  refine (PrimeSpectrum.isTopologicalBasis_basic_opens (R := MvPolynomial ℕ k)).dense_iff.2 ?_
  rintro _ ⟨f, rfl⟩ hf
  have hfX : PrimeSpectrum.basicOpen (f * X 0) ≠ ⊥ := by
    rw [Ne, PrimeSpectrum.basicOpen_eq_bot_iff, (Commute.all _ _).isNilpotent_mul_right_iff
      isRegular_X.right.mem_nonZeroDivisorsRight, ← PrimeSpectrum.basicOpen_eq_bot_iff]
    exact (TopologicalSpace.Opens.ne_bot_iff_nonempty _).2 hf
  obtain ⟨p, hp⟩ := (TopologicalSpace.Opens.ne_bot_iff_nonempty _).1 hfX
  rw [PrimeSpectrum.basicOpen_mul] at hp
  exact ⟨p, hp.1, TopologicalSpace.Opens.mem_iSup.2 ⟨0, hp.2⟩⟩

/-- `x_j^{j+2}` kills `B`. -/
private theorem X_pow_smul_eq_zero (j : ℕ) (b : Bmod k) :
    (X j ^ (j + 2) : MvPolynomial ℕ k) • b = 0 := by
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective (b : B k)
  rw [smul_mk, Ideal.Quotient.eq_zero_iff_mem, X_pow_eq_monomial]
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
          (p.val.isPrime.mem_of_pow_mem _ h), X_pow_smul_eq_zero k j m⟩
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

/-- **The inclusion `U ⟶ Spec A` is not quasi-compact** when `k ≠ 0`. -/
theorem not_quasiCompact_ι [Nontrivial k] : ¬ QuasiCompact (U k).ι := by
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
  obtain ⟨m, hm⟩ := Ideal.exists_maximal k
  let φ : MvPolynomial ℕ k →+* MvPolynomial ℕ (k ⧸ m) :=
    eval₂Hom (C.comp (Ideal.Quotient.mk m)) fun i ↦ if i ≤ N then 0 else X i
  let q : PrimeSpectrum (MvPolynomial ℕ k) := ⟨RingHom.ker φ, RingHom.ker_isPrime _⟩
  have hq : q ∈ U k := TopologicalSpace.Opens.mem_iSup.2 ⟨N + 1, by
    rw [PrimeSpectrum.mem_basicOpen, RingHom.mem_ker]
    simp [φ, X_ne_zero]⟩
  obtain ⟨j, hjt, hj⟩ := Set.mem_iUnion₂.1 (ht hq)
  apply (PrimeSpectrum.mem_basicOpen _ _).1 hj
  have hjN : j ≤ N := Finset.le_sup (f := id) hjt
  rw [RingHom.mem_ker]
  simp [φ, hjN]

end TauCeti.StrictTransformNonQuasiCompactExample
