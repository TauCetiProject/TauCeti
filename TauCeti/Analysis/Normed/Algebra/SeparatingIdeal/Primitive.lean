/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Algebra.SeparatingIdeal.Basic
public import TauCeti.Analysis.Normed.Module.Simple
public import TauCeti.Analysis.Normed.Module.Simple.Existence
public import TauCeti.RingTheory.Ideal.Primitive

/-!
# Separating ideals and primitive ideals

A separating ideal `J` of a unital complex Banach algebra `B` can act nontrivially only on
finite-dimensional simple modules. Equivalently, if `J` is not contained in a primitive ideal
`P` of `B`, then the primitive quotient `B ⧸ P` is finite-dimensional. This is the reduction to
primitive quotients in the structure theory of separating ideals, which in turn yields the
automatic continuity of surjective homomorphisms onto, and derivations on, semisimple Banach
algebras.

The proof runs the right nest of `J` along a sequence `b` chosen so that the kernels on an
infinite-dimensional simple Banach module `E` of the products `b (n - 1) ⋯ b 0` strictly
increase. The closure of `J b (n - 1) ⋯ b 0` annihilates exactly that kernel, so the nest never
stabilizes. The sequence is built from Rickart's complex Jacobson density when no element of
`B` acts on `E` with nonzero finite rank; otherwise it uses elements `1 - f` with `f` of finite
rank. Algebraic simple modules are reduced to simple Banach modules by
`IsSimpleModule.exists_complete_norm`.

## Main results

* `Submodule.IsSeparatingIdeal.finiteDimensional_of_isSimpleModule`: a simple `B`-module on
  which some element of a separating ideal acts nontrivially is finite-dimensional.
* `Submodule.IsSeparatingIdeal.finiteDimensional_quotient_of_isPrimitive`: if a separating
  ideal is not contained in a primitive ideal `P`, then `B ⧸ P` is finite-dimensional.

## References

* H. G. Dales, *Banach Algebras and Automatic Continuity*, §5.2: separating ideals and their
  primitive quotients.
* A. M. Sinclair, *Automatic Continuity of Linear Operators*, London Math. Soc. Lecture Note
  Series 21.
-/

public section

open Filter

namespace Submodule.IsSeparatingIdeal

section Banach

variable {B E : Type*} [NormedRing B] [NormedAlgebra ℂ B] [CompleteSpace B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [Module B E] [IsScalarTower ℂ B E] [ContinuousSMul B E] [IsSimpleModule B E]

/-- If `p` acts on a simple complex Banach module with infinite-dimensional range, then some
left multiple `b * p` kills a vector that `p` does not kill, and `b * p` still acts with
infinite-dimensional range. -/
private theorem exists_mul_smul_eq_zero (p : B)
    (hp : ¬ FiniteDimensional ℂ (LinearMap.range (Algebra.lsmul ℂ ℂ E p))) :
    ∃ b : B, ∃ x : E, p • x ≠ 0 ∧ (b * p) • x = 0 ∧
      ¬ FiniteDimensional ℂ (LinearMap.range (Algebra.lsmul ℂ ℂ E (b * p))) := by
  obtain ⟨x, hx⟩ : ∃ x : E, p • x ≠ 0 := by
    by_contra! h
    have h0 : Algebra.lsmul ℂ ℂ E p = 0 := LinearMap.ext fun y ↦ by simpa using h y
    rw [h0, LinearMap.range_zero] at hp
    exact hp inferInstance
  by_cases hfin : ∃ s : B, ∃ ξ : E, s • ξ ≠ 0 ∧
      FiniteDimensional ℂ (LinearMap.range (Algebra.lsmul ℂ ℂ E s))
  · -- Some `s` has nonzero finite rank. Transitivity gives `f = a * s * c` of finite rank
    -- fixing `p • x`; then `b = 1 - f` kills `p • x` and has finite-dimensional kernel.
    obtain ⟨s, ξ, hsξ, hs⟩ := hfin
    obtain ⟨a, ha⟩ := IsSimpleModule.toSpanSingleton_surjective B hsξ (p • x)
    obtain ⟨c, hc⟩ := IsSimpleModule.toSpanSingleton_surjective B hx ξ
    rw [LinearMap.toSpanSingleton_apply] at ha hc
    have hf : (a * s * c) • p • x = p • x := by rw [mul_smul, mul_smul, hc, ha]
    have hfin : FiniteDimensional ℂ (LinearMap.range (Algebra.lsmul ℂ ℂ E (a * s * c))) := by
      refine Submodule.finiteDimensional_of_le
        (S₂ := (LinearMap.range (Algebra.lsmul ℂ ℂ E s)).map (Algebra.lsmul ℂ ℂ E a)) ?_
      rintro _ ⟨y, rfl⟩
      exact ⟨s • c • y, ⟨c • y, Algebra.lsmul_apply ..⟩, by simp⟩
    refine ⟨1 - a * s * c, x, hx, by rw [mul_smul, sub_smul, one_smul, hf, sub_self],
      fun h ↦ hp ?_⟩
    rw [← Submodule.fg_iff_finiteDimensional] at h ⊢
    refine Submodule.fg_of_fg_map_of_fg_inf_ker (Algebra.lsmul ℂ ℂ E (1 - a * s * c)) ?_ ?_
    · rwa [← LinearMap.range_comp, ← Module.End.mul_eq_comp, ← map_mul]
    · rw [Submodule.fg_iff_finiteDimensional]
      refine Submodule.finiteDimensional_of_le
        (S₂ := LinearMap.range (Algebra.lsmul ℂ ℂ E (a * s * c))) ?_
      rintro y ⟨-, hy⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, Algebra.lsmul_apply, sub_smul, one_smul,
        sub_eq_zero] at hy
      exact ⟨y, (Algebra.lsmul_apply ..).trans hy.symm⟩
  · -- Every nonzero element has infinite rank. Density on `p • x` and an independent vector
    -- `p • y` of the range of `p` gives `b` killing the first and fixing the second.
    push Not at hfin
    obtain ⟨w, hwR, hw⟩ : ∃ w ∈ LinearMap.range (Algebra.lsmul ℂ ℂ E p), w ∉ ℂ ∙ (p • x) := by
      by_contra! h
      have heq : LinearMap.range (Algebra.lsmul ℂ ℂ E p) = ℂ ∙ (p • x) :=
        le_antisymm h ((Submodule.span_singleton_le_iff_mem _ _).2 ⟨x, Algebra.lsmul_apply ..⟩)
      rw [heq] at hp
      exact hp inferInstance
    obtain ⟨y, rfl⟩ := hwR
    rw [Algebra.lsmul_apply] at hw
    have hli : LinearIndependent ℂ ![p • x, p • y] :=
      (LinearIndependent.pair_iff' hx).2 fun r hr ↦
        hw (Submodule.mem_span_singleton.2 ⟨r, hr⟩)
    obtain ⟨b, hb⟩ := hli.exists_smul_eq_of_completeSpace (A := B) ![0, p • y]
    have hy : p • y ≠ 0 := fun h ↦ hw (h ▸ Submodule.zero_mem _)
    have hb1 : b • p • y = p • y := by simpa using hb 1
    refine ⟨b, x, hx, by simpa [mul_smul] using hb 0, hfin _ y ?_⟩
    rwa [mul_smul, hb1]

/-- The Banach-module form of `finiteDimensional_of_isSimpleModule`. -/
private theorem finiteDimensional_of_isSimpleModule_of_completeSpace {J : Submodule ℂ B}
    (hJ : J.IsSeparatingIdeal) {j : B} (hj : j ∈ J) {ξ : E} (hjξ : j • ξ ≠ 0) :
    FiniteDimensional ℂ E := by
  by_contra hE
  -- Every nonzero vector is moved by some element of `J`.
  have hJ' (η : E) (hη : η ≠ 0) : ∃ j' ∈ J, j' • η ≠ 0 := by
    obtain ⟨a, ha⟩ := IsSimpleModule.toSpanSingleton_surjective B hη ξ
    rw [LinearMap.toSpanSingleton_apply] at ha
    exact ⟨j * a, hJ.mul_mem_right a hj, by rwa [mul_smul, ha]⟩
  -- Iterating `exists_mul_smul_eq_zero` from `1` gives products `Q n = b (n - 1) ⋯ b 0` whose
  -- kernels on `E` strictly increase.
  have h1 : ¬ FiniteDimensional ℂ (LinearMap.range (Algebra.lsmul ℂ ℂ E (1 : B))) := by
    rw [map_one, Module.End.one_eq_id, LinearMap.range_id]
    exact fun h ↦ hE (Module.Finite.equiv Submodule.topEquiv)
  choose g x hx hgx hg using fun p : {p : B //
    ¬ FiniteDimensional ℂ (LinearMap.range (Algebra.lsmul ℂ ℂ E p))} ↦
      exists_mul_smul_eq_zero p.1 p.2
  let Q : ℕ → {p : B // ¬ FiniteDimensional ℂ (LinearMap.range (Algebra.lsmul ℂ ℂ E p))} :=
    fun n ↦ Nat.rec ⟨1, h1⟩ (fun _ p ↦ ⟨g p * p.1, hg p⟩) n
  let b : ℕ → B := fun n ↦ g (Q n)
  let V : ℕ → Submodule ℂ B := fun n ↦
    (J.map ((List.range n).map fun i ↦ LinearMap.mulRight ℂ (b i)).prod).topologicalClosure
  have hprod (n : ℕ) (y : B) :
      ((List.range n).map fun i ↦ LinearMap.mulRight ℂ (b i)).prod y = y * (Q n).1 := by
    induction n generalizing y with
    | zero => simp [Q]
    | succ n ih => simp [List.range_succ, ih, b, Q, mul_assoc]
  -- The closure of `J * Q n` annihilates exactly the kernel of `Q n`.
  have key (n : ℕ) (η : E) : (∀ c ∈ V n, c • η = 0) ↔ (Q n).1 • η = 0 := by
    refine ⟨fun h ↦ ?_, fun h c hc ↦ ?_⟩
    · by_contra hη
      obtain ⟨j', hj', hj'η⟩ := hJ' _ hη
      rw [← mul_smul, ← hprod] at hj'η
      exact hj'η (h _ (Submodule.le_topologicalClosure _ (Submodule.mem_map_of_mem hj')))
    · let q : B →L[ℂ] E := (ContinuousLinearMap.id ℂ B).smulRight η
      have hle : J.map ((List.range n).map fun i ↦ LinearMap.mulRight ℂ (b i)).prod ≤
          LinearMap.ker (q : B →ₗ[ℂ] E) := by
        rintro _ ⟨y, -, rfl⟩
        simp [q, hprod, mul_smul, h]
      simpa [q] using Submodule.topologicalClosure_minimal _ hle q.isClosed_ker hc
  obtain ⟨N, hN⟩ := eventuallyConst_atTop_nat.1 (hJ.eventuallyConst_right b)
  have hV : V (N + 1) = V N := hN N le_rfl
  exact hx (Q N) ((key N _).1 (hV ▸ (key (N + 1) _).2 (hgx (Q N))))

end Banach

variable {B : Type*} [NormedRing B] [NormedAlgebra ℂ B] [CompleteSpace B]

/-- **Separating ideals act only on finite-dimensional simple modules.** Let `J` be a
separating ideal of a unital complex Banach algebra `B` and `M` a simple left `B`-module, with
no topology assumed. If some element of `J` acts nontrivially on `M`, then `M` is
finite-dimensional over `ℂ`. -/
theorem finiteDimensional_of_isSimpleModule {M : Type*} [AddCommGroup M] [Module B M]
    [Module ℂ M] [IsScalarTower ℂ B M] [IsSimpleModule B M] {J : Submodule ℂ B}
    (hJ : J.IsSeparatingIdeal) {j : B} (hj : j ∈ J) {m : M} (hjm : j • m ≠ 0) :
    FiniteDimensional ℂ M := by
  obtain ⟨p, hn, hc, hb⟩ := IsSimpleModule.exists_complete_norm (𝕜 := ℂ) (A := B)
    (inferInstance : IsSimpleModule B M)
  let := p.toNormedAddCommGroup
  let : NormedSpace ℂ M := ⟨fun c x ↦ (norm_smul c x).le⟩
  exact finiteDimensional_of_isSimpleModule_of_completeSpace hJ hj hjm

/-- **Separating ideals have finite-dimensional primitive quotients.** If a separating ideal
`J` of a unital complex Banach algebra `B` is not contained in a primitive ideal `P`, then
`B ⧸ P` is finite-dimensional over `ℂ`. -/
theorem finiteDimensional_quotient_of_isPrimitive {J : Submodule ℂ B}
    (hJ : J.IsSeparatingIdeal) {P : Ideal B} (hP : P.IsPrimitive)
    (hJP : ¬ J ≤ P.restrictScalars ℂ) : FiniteDimensional ℂ (B ⧸ P) := by
  obtain ⟨L, hL, rfl⟩ := (Ideal.isPrimitive_iff_exists_isMaximal P).mp hP
  have : IsSimpleModule B (B ⧸ L) := isSimpleModule_iff_isCoatom.mpr (Ideal.isMaximal_def.mp hL)
  obtain ⟨j, hj, hjP⟩ := IsConcreteLE.not_le_iff_exists.mp hJP
  obtain ⟨m, hm⟩ : ∃ m : B ⧸ L, j • m ≠ 0 := by
    by_contra! h
    exact hjP (Module.mem_annihilator.mpr h)
  have := finiteDimensional_of_isSimpleModule hJ hj hm
  -- `B ⧸ P` embeds into the finite-dimensional algebra of linear endomorphisms of `B ⧸ L`.
  let φ : B →ₗ[ℂ] Module.End ℂ (B ⧸ L) := (Algebra.lsmul ℂ ℂ (B ⧸ L)).toLinearMap
  have hker : LinearMap.ker φ = (Module.annihilator B (B ⧸ L)).restrictScalars ℂ := by
    ext a
    simp [φ, Module.mem_annihilator, LinearMap.ext_iff]
  let ψ := ((Module.annihilator B (B ⧸ L)).restrictScalars ℂ).liftQ φ hker.ge ∘ₗ
    (Submodule.Quotient.restrictScalarsEquiv ℂ (Module.annihilator B (B ⧸ L))).symm.toLinearMap
  refine Module.Finite.of_injective ψ ?_
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_comp, Submodule.ker_liftQ_eq_bot _ _ _ hker.le,
    Submodule.comap_bot, LinearEquiv.ker]

end Submodule.IsSeparatingIdeal
