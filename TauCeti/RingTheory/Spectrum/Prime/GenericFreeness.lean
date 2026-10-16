/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.Algebra.Polynomial.Basis
public import TauCeti.RingTheory.Spectrum.Prime.FreeLocus
public import TauCeti.RingTheory.Spectrum.Prime.Topology

/-!
# Generic freeness

Let `A` be a reduced Noetherian ring, `B` a finitely generated `A`-algebra and `M` a finite
`B`-module. Then `M`, viewed as an `A`-module, is free at every prime of an open neighbourhood of
the minimal primes of `A`; in particular the interior of its free locus is dense in `Spec A`.
Over a Noetherian domain this says that `M_q` is free over `A_q` for every prime `q` in some
nonempty basic open set.

The module `M` is usually not finitely generated over `A`, so openness of the free locus of a
finitely presented module does not apply directly. Instead, the proof is by induction on the
number of generators of `B`. A finite module `M` over a polynomial ring `R[X]`, with generators
`m₁, …, mₜ`, is filtered by the `R`-submodules `F j` spanned by the `X ^ i • mₖ` with `i < j`.
Each subquotient `F (j + 1) ⧸ F j` is a quotient of `Rᵗ` by the submodule `K j` of coefficient
vectors `c` with `∑ cₖ • X ^ j • mₖ ∈ F j`. Multiplication by `X` shows that `K j` increases with
`j`, so by Noetherianity only finitely many distinct subquotients occur. The induction hypothesis
makes each of them free on an open neighbourhood of the minimal primes, and the finite
intersection of these sets is an open neighbourhood on which every subquotient, hence `M` itself,
is free.

## Main declarations

* `Module.freeLocus_mem_nhds_of_mem_minimalPrimes`: a finite module over a finitely generated
  algebra over a reduced Noetherian ring is free over that ring near every minimal prime.
* `Module.dense_interior_freeLocus_of_finiteType`: such a module is free over the base on a
  dense open subset of its spectrum.

## References

* H. Matsumura, *Commutative Ring Theory*, Theorem 24.1.
* The Stacks Project, Tag 051R.
-/

public section

open Polynomial Topology

namespace Module

universe uA uR uM

variable {A : Type uA} [CommRing A]

/-- If every finite `R`-module is free over `A` near each minimal prime of `A`, then so is every
finite module over the polynomial ring `R[X]`. -/
private theorem freeLocus_mem_nhds_polynomial {R : Type uR} [CommRing R] [Algebra A R]
    [IsNoetherianRing R]
    (hR : ∀ (N : Type uR) [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower A R N]
      [Module.Finite R N] (p : Ideal A) (hp : p ∈ minimalPrimes A),
      freeLocus A N ∈ 𝓝 ⟨p, hp.1.1⟩)
    (M : Type uM) [AddCommGroup M] [Module R[X] M] [Module A M] [IsScalarTower A R[X] M]
    [Module.Finite R[X] M] (p : Ideal A) (hp : p ∈ minimalPrimes A) :
    freeLocus A M ∈ 𝓝 ⟨p, hp.1.1⟩ := by
  classical
  let _ : Module R M := Module.restrictScalars R R[X] M
  have : IsScalarTower R R[X] M := IsScalarTower.restrictScalars R R[X] M
  have : IsScalarTower A R M := IsScalarTower.of_algebraMap_smul fun a m ↦
    (congrArg (fun q : R[X] ↦ q • m)
      (IsScalarTower.algebraMap_apply A R R[X] a).symm).trans
      (IsScalarTower.algebraMap_smul R[X] a m)
  obtain ⟨t, m, hm⟩ := Module.Finite.exists_fin (R := R[X]) (M := M)
  -- `φ j c = ∑ cₖ • X ^ j • mₖ`, and `F j` is spanned by the images of `φ i` for `i < j`.
  let φ : ℕ → (Fin t → R) →ₗ[R] M := fun j ↦
    Fintype.linearCombination R fun k ↦ (X ^ j : R[X]) • m k
  let F : ℕ → Submodule R M := fun j ↦ ⨆ i < j, LinearMap.range (φ i)
  let lX : M →ₗ[R] M := Algebra.lsmul R R M (X : R[X])
  have hφX (j : ℕ) : φ (j + 1) = lX ∘ₗ φ j := by
    ext c
    simp only [φ, lX, LinearMap.comp_apply, Algebra.lsmul_apply,
      Fintype.linearCombination_apply, Finset.smul_sum, pow_succ', mul_smul]
    exact Finset.sum_congr rfl fun k _ ↦ (smul_comm _ _ _).symm
  have hFmono : Monotone F := fun i j hij ↦
    biSup_mono fun _ hk ↦ lt_of_lt_of_le hk hij
  have hFsucc (j : ℕ) : F (j + 1) = F j ⊔ LinearMap.range (φ j) := Nat.iSup_lt_succ _ j
  have hF0 : F 0 = ⊥ := by simp [F]
  have hFX (j : ℕ) : (F j).map lX ≤ F (j + 1) := by
    simp only [F, Submodule.map_iSup, iSup_le_iff]
    intro i hi
    rw [← LinearMap.range_comp, ← hφX]
    exact le_iSup₂_of_le (i + 1) (by omega) le_rfl
  have hFtop : ⨆ j, F j = ⊤ := by
    have hspan : Submodule.span R (Set.range fun i : ℕ ↦ (X ^ i : R[X])) = ⊤ := by
      simpa [← Polynomial.X_pow_eq_monomial] using (Polynomial.basisMonomials R).span_eq
    rw [eq_top_iff, ← Submodule.restrictScalars_top R R[X] M, ← hm,
      ← Submodule.span_smul_of_span_eq_top hspan, Submodule.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, _, ⟨k, rfl⟩, rfl⟩
    refine Submodule.mem_iSup_of_mem (i + 1) (Submodule.mem_iSup_of_mem i
      (Submodule.mem_iSup_of_mem (Nat.lt_succ_self i) ⟨Pi.single k 1, ?_⟩))
    simp [φ, Fintype.linearCombination_apply, Pi.single_apply]
  -- `K j` is the module of relations of the `j`-th subquotient; it increases with `j`.
  let K : ℕ →o Submodule R (Fin t → R) :=
    ⟨fun j ↦ (F j).comap (φ j), monotone_nat_of_le_succ fun j c hc ↦ by
      rw [Submodule.mem_comap, hφX, LinearMap.comp_apply]
      exact hFX j (Submodule.mem_map_of_mem hc)⟩
  obtain ⟨j₀, hj₀⟩ := monotone_stabilizes_iff_noetherian.mpr inferInstance K
  -- The `j`-th subquotient of the filtration, viewed over `A`, is `Rᵗ ⧸ K j`.
  let N : ℕ → Submodule A M := fun j ↦ (F j).restrictScalars A
  have hNmono : Monotone N := fun _ _ hij ↦ Submodule.restrictScalars_mono A (hFmono hij)
  have hsub (j : ℕ) : freeLocus A ((Fin t → R) ⧸ K j) =
      freeLocus A (N (j + 1) ⧸ (N j).submoduleOf (N (j + 1))) := by
    have hNsucc : N (j + 1) = N j ⊔ LinearMap.range ((φ j).restrictScalars A) := by
      simp only [N, hFsucc, LinearMap.range_restrictScalars, Submodule.restrictScalars_sup]
    have hmem (c : Fin t → R) : (φ j).restrictScalars A c ∈ N (j + 1) := by
      rw [hNsucc]
      exact Submodule.mem_sup_right ⟨c, rfl⟩
    let ψ : (Fin t → R) →ₗ[A] N (j + 1) ⧸ (N j).submoduleOf (N (j + 1)) :=
      ((N j).submoduleOf (N (j + 1))).mkQ ∘ₗ ((φ j).restrictScalars A).codRestrict _ hmem
    have hψ : Function.Surjective ψ := by
      apply LinearMap.range_eq_top.mp
      simp only [ψ, LinearMap.range_comp, Submodule.map_mkQ_eq_top,
        LinearMap.range_codRestrict]
      exact
        (Submodule.submoduleOf_sup_of_le (hNmono j.le_succ)
          (le_sup_right.trans_eq hNsucc.symm)).symm.trans
          (Submodule.submoduleOf_eq_top.mpr hNsucc.le)
    have hker : LinearMap.ker ψ = (K j).restrictScalars A := by
      ext c
      simp only [LinearMap.mem_ker, ψ, LinearMap.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero]
      simp only [N, K, OrderHom.coe_mk, Submodule.restrictScalars_mem, Submodule.submoduleOf,
        Submodule.mem_comap, LinearMap.codRestrict_apply, LinearMap.restrictScalars_apply,
        Submodule.coe_subtype]
    exact freeLocus_congr ((Submodule.Quotient.restrictScalarsEquiv A (K j)).symm ≪≫ₗ
      Submodule.quotEquivOfEq _ _ hker.symm ≪≫ₗ ψ.quotKerEquivOfSurjective hψ)
  -- Only the finitely many subquotients with `j ≤ j₀` matter.
  let U := ⋂ j ∈ Finset.range (j₀ + 1), interior (freeLocus A ((Fin t → R) ⧸ K j))
  have hU : U ∈ 𝓝 ⟨p, hp.1.1⟩ :=
    (isOpen_biInter_finset fun _ _ ↦ isOpen_interior).mem_nhds <| Set.mem_iInter₂.mpr
      fun j _ ↦ mem_interior_iff_mem_nhds.mpr (hR ((Fin t → R) ⧸ K j) p hp)
  refine Filter.mem_of_superset hU (subset_trans ?_ (iInter_freeLocus_subquotient_subset_freeLocus
    N hNmono (by simp [N, hF0]) ?_))
  · intro q hq
    rw [Set.mem_iInter]
    intro j
    have hK : K j = K (min j j₀) := by
      rcases le_total j j₀ with h | h
      · rw [min_eq_left h]
      · rw [min_eq_right h, hj₀ j h]
    rw [← hsub, hK]
    have hj : min j j₀ ∈ Finset.range (j₀ + 1) := Finset.mem_range.mpr (by omega)
    exact interior_subset (Set.mem_iInter₂.mp hq (min j j₀) hj)
  · simp only [N, ← Submodule.restrictScalars_iSup, hFtop, Submodule.restrictScalars_top]

/-- Freeness of finite modules near the minimal primes of `A` transfers along a surjective
algebra map. -/
private theorem freeLocus_mem_nhds_of_surjective {R S : Type*} [CommRing R] [CommRing S]
    [Algebra A R] [Algebra A S] (f : R →ₐ[A] S) (hf : Function.Surjective f)
    (hR : ∀ (N : Type uM) [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower A R N]
      [Module.Finite R N] (p : Ideal A) (hp : p ∈ minimalPrimes A),
      freeLocus A N ∈ 𝓝 ⟨p, hp.1.1⟩)
    (M : Type uM) [AddCommGroup M] [Module S M] [Module A M] [IsScalarTower A S M]
    [Module.Finite S M] (p : Ideal A) (hp : p ∈ minimalPrimes A) :
    freeLocus A M ∈ 𝓝 ⟨p, hp.1.1⟩ := by
  let _ : Algebra R S := f.toRingHom.toAlgebra
  let _ : Module R M := Module.compHom M f.toRingHom
  have : IsScalarTower R S M := IsScalarTower.of_compHom R S M
  have : IsScalarTower A R M := IsScalarTower.of_algebraMap_smul fun a m ↦
    (congrArg (fun s : S ↦ s • m) (f.commutes a)).trans
      (IsScalarTower.algebraMap_smul S a m)
  have : Module.Finite R S := Module.Finite.of_surjective (Algebra.linearMap R S) hf
  have : Module.Finite R M := Module.Finite.trans S M
  exact hR M p hp

/-- **Generic freeness.** Let `A` be a reduced Noetherian ring, `B` a finitely generated
`A`-algebra and `M` a finite `B`-module. Then `M` is free over `A` on a neighbourhood of every
minimal prime of `A`.

For a Noetherian domain `A` this means that there is a nonzero `a : A` such that `M_q` is free
over `A_q` for every prime `q` not containing `a`. -/
theorem freeLocus_mem_nhds_of_mem_minimalPrimes [IsNoetherianRing A] [IsReduced A]
    {B : Type*} [CommRing B] [Algebra A B] [Algebra.FiniteType A B]
    (M : Type uM) [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
    [Module.Finite B M] {p : Ideal A} (hp : p ∈ minimalPrimes A) :
    freeLocus A M ∈ 𝓝 ⟨p, hp.1.1⟩ := by
  -- Finite modules over polynomial rings in finitely many variables.
  have key (n : ℕ) : ∀ (N : Type uA) [AddCommGroup N] [Module (MvPolynomial (Fin n) A) N]
      [Module A N] [IsScalarTower A (MvPolynomial (Fin n) A) N]
      [Module.Finite (MvPolynomial (Fin n) A) N] (p : Ideal A) (hp : p ∈ minimalPrimes A),
      freeLocus A N ∈ 𝓝 ⟨p, hp.1.1⟩ := by
    induction n with
    | zero =>
      intro N _ _ _ _ _ p hp
      have : Module.Finite A (MvPolynomial (Fin 0) A) :=
        Module.Finite.equiv (MvPolynomial.isEmptyAlgEquiv A (Fin 0)).symm.toLinearEquiv
      have : Module.Finite A N := Module.Finite.trans (MvPolynomial (Fin 0) A) N
      have : FinitePresentation A N := Module.finitePresentation_of_finite A N
      exact isOpen_freeLocus.mem_nhds (mem_freeLocus_of_mem_minimalPrimes N hp)
    | succ n ih =>
      exact freeLocus_mem_nhds_of_surjective (MvPolynomial.finSuccEquiv A n).symm.toAlgHom
        (MvPolynomial.finSuccEquiv A n).symm.surjective (freeLocus_mem_nhds_polynomial ih)
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp ‹Algebra.FiniteType A B›
  refine freeLocus_mem_nhds_of_surjective (aevalTower f 0) (fun b ↦ ?_)
    (freeLocus_mem_nhds_polynomial (key n)) M p hp
  obtain ⟨q, rfl⟩ := hf b
  exact ⟨C q, aevalTower_C _ _ _⟩

/-- **Generic freeness.** Let `A` be a reduced Noetherian ring, `B` a finitely generated
`A`-algebra and `M` a finite `B`-module. Then `M` is free over `A` on a dense open subset of
`Spec A`. -/
theorem dense_interior_freeLocus_of_finiteType [IsNoetherianRing A] [IsReduced A]
    {B : Type*} [CommRing B] [Algebra A B] [Algebra.FiniteType A B]
    (M : Type uM) [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
    [Module.Finite B M] : Dense (interior (freeLocus A M)) :=
  PrimeSpectrum.dense_of_forall_mem_minimalPrimes fun _ hp ↦
    mem_interior_iff_mem_nhds.mpr (freeLocus_mem_nhds_of_mem_minimalPrimes (B := B) M hp)

end Module
