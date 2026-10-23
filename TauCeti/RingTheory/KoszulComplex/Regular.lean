/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Regular.RegularSequence
public import TauCeti.RingTheory.KoszulComplex.Basic

/-!
# Koszul complexes of weakly regular sequences

For a weakly regular sequence `x = (x₁, …, xₙ)` in a commutative ring `R`, the Koszul complex
`K(x)` is acyclic in positive degrees: `Hₖ(K(x)) = 0` for `k > 0`. Together with
`H₀(K(x)) ≃ R ⧸ (x₁, …, xₙ)` (`TauCeti.koszulComplex.homologyZeroEquivSpan`), this says that the
complex of finite free modules `K(x)ₖ = ⋀ᵏ Rⁿ` resolves `R ⧸ (x₁, …, xₙ)`.

The proof adjoins one element at a time. For a linear functional `φ : M → R` and `x : R`, the
functional `(m, r) ↦ φ(m) + r x` on `M × R` is the Koszul complex `K(φ, x)` of `φ` with `x`
adjoined. Writing `e = (0, 1)`, every element of `⋀ᵏ⁺¹ (M × R)` is uniquely `a + e ∧ b` with
`a ∈ ⋀ᵏ⁺¹ M` and `b ∈ ⋀ᵏ M`, and the Koszul differential is
`d(a + e ∧ b) = (d a + x b) - e ∧ d b`. Hence a cycle `a + e ∧ b` of `K(φ, x)` has `d b = 0` and
`x b = -d a`. If `K(φ)` is exact at `⋀ᵏ⁺¹ M` and `b` is a boundary, then `a + e ∧ b` is a
boundary. In degree `k + 2` the cycle `b` is a boundary when `Hₖ₊₁(K(φ)) = 0`; in degree one,
`x b ∈ φ(M)` forces `b ∈ φ(M)` when `x` is a nonzerodivisor on `R ⧸ φ(M) ≃ H₀(K(φ))`. For a
weakly regular sequence, induction on its length provides these hypotheses: the higher homology
of the shorter sequence vanishes, and the last element is a nonzerodivisor on its zeroth homology
`R ⧸ (x₁, …, xₙ₋₁)`.

## Main declarations

* `TauCeti.exact_koszulDifferential_of_retract`: exactness of a Koszul complex passes to a
  retract along linear maps compatible with the functionals.
* `TauCeti.exact_koszulDifferential_coprod_succ`,
  `TauCeti.exact_koszulDifferential_coprod_zero`: adjoining an element `x` to `φ` preserves
  vanishing of `Hₖ₊₂`, and preserves vanishing of `H₁` when `x` is a nonzerodivisor on
  `R ⧸ φ(M)`.
* `TauCeti.koszulComplex.exactAt_succ_iff`: `Hₖ₊₁(K(φ)) = 0` exactly when the Koszul
  differentials out of and into `⋀ᵏ⁺¹ M` are exact.
* `TauCeti.koszulComplex.exactAt_of_isWeaklyRegular`: **the Koszul complex of a weakly regular
  sequence is acyclic in positive degrees.**

## References

* [The Stacks Project, Tags 0626 and 062F](https://stacks.math.columbia.edu/tag/062F)
-/

public section

noncomputable section

universe u v

open CategoryTheory CliffordAlgebra

namespace TauCeti

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

section Retract

variable {N : Type*} [AddCommGroup N] [Module R N]

/-- **Exactness passes to retracts.** If `g : M → N` has a retraction `h` and `ψ = φ ∘ h` (so
that also `φ = ψ ∘ g`), then the Koszul complex `K(φ)` is a retract of `K(ψ)`, and exactness of
`K(ψ)` at `⋀ⁿ⁺¹ N` implies exactness of `K(φ)` at `⋀ⁿ⁺¹ M`. -/
theorem exact_koszulDifferential_of_retract {φ : Module.Dual R M} {ψ : Module.Dual R N}
    (g : M →ₗ[R] N) (h : N →ₗ[R] M) (hhg : h ∘ₗ g = LinearMap.id) (hψ : φ ∘ₗ h = ψ) (n : ℕ)
    (hex : Function.Exact (koszulDifferential ψ (n + 1)) (koszulDifferential ψ n)) :
    Function.Exact (koszulDifferential φ (n + 1)) (koszulDifferential φ n) := by
  have hφ : ψ ∘ₗ g = φ := by rw [← hψ, LinearMap.comp_assoc, hhg, LinearMap.comp_id]
  refine fun z ↦ ⟨fun hz ↦ ?_, ?_⟩
  · obtain ⟨y, hy⟩ := (hex (exteriorPower.map (n + 1) g z)).1 (by
      rw [koszulDifferential_map, hφ, hz, map_zero])
    refine ⟨exteriorPower.map (n + 2) h y, ?_⟩
    rw [koszulDifferential_map, hψ, hy, ← LinearMap.comp_apply, ← exteriorPower.map_comp, hhg,
      exteriorPower.map_id, LinearMap.id_apply]
  · rintro ⟨y, rfl⟩
    exact koszulDifferential_koszulDifferential φ n y

end Retract

section Adjoin

/-! ### Adjoining one element to a linear functional -/

variable (φ : Module.Dual R M) (x : R)

/-- The contraction by `φ + x · snd` on the image of `⋀ M` is the contraction by `φ`. -/
private theorem contractLeft_coprod_map_inl (w : ExteriorAlgebra R M) :
    contractLeft (Q := (0 : QuadraticForm R (M × R)))
        (φ.coprod (LinearMap.toSpanSingleton R R x)) (ExteriorAlgebra.map (LinearMap.inl R M R) w) =
      ExteriorAlgebra.map (LinearMap.inl R M R)
        (contractLeft (Q := (0 : QuadraticForm R M)) φ w) := by
  rw [ExteriorAlgebra.contractLeft_map, LinearMap.coprod_inl]

/-- The contraction by `φ + x · snd` on `e ∧ w`: `d(e ∧ w) = x w - e ∧ d w`. -/
private theorem contractLeft_coprod_ι_inr_mul (w : ExteriorAlgebra R (M × R)) :
    contractLeft (Q := (0 : QuadraticForm R (M × R)))
        (φ.coprod (LinearMap.toSpanSingleton R R x))
        (ExteriorAlgebra.ι R (LinearMap.inr R M R 1) * w) =
        x • w - ExteriorAlgebra.ι R (LinearMap.inr R M R 1) *
          contractLeft (Q := (0 : QuadraticForm R (M × R)))
            (φ.coprod (LinearMap.toSpanSingleton R R x)) w := by
  rw [contractLeft_ι_mul]
  simp

/-- The `⋀ M`-component of `d z` is `d a + x b`, where `z = a + e ∧ b`. -/
private theorem map_fst_contractLeft_coprod (z : ExteriorAlgebra R (M × R)) :
    ExteriorAlgebra.map (LinearMap.fst R M R)
        (contractLeft (Q := (0 : QuadraticForm R (M × R)))
          (φ.coprod (LinearMap.toSpanSingleton R R x)) z) =
      contractLeft (Q := (0 : QuadraticForm R M)) φ
          (ExteriorAlgebra.map (LinearMap.fst R M R) z) +
        x • ExteriorAlgebra.map (LinearMap.fst R M R)
          (contractLeft (Q := (0 : QuadraticForm R (M × R))) (LinearMap.snd R M R) z) := by
  have hFI : Function.LeftInverse (ExteriorAlgebra.map (LinearMap.fst R M R))
      (ExteriorAlgebra.map (LinearMap.inl R M R)) :=
    ExteriorAlgebra.leftInverse_map_iff.2 fun _ ↦ rfl
  conv_lhs => rw [← ExteriorAlgebra.map_inl_map_fst_add_ι_inr_mul_contractLeft_snd z]
  rw [map_add, contractLeft_coprod_map_inl, contractLeft_coprod_ι_inr_mul,
    contractLeft_coprod_map_inl, map_add, map_sub, map_smul, hFI, hFI, map_mul]
  simp

/-- The `e`-component `b` of `z = a + e ∧ b` satisfies `d b = -b'`, where `b'` is the
`e`-component of `d z`. -/
private theorem contractLeft_map_fst_contractLeft_snd (z : ExteriorAlgebra R (M × R)) :
    contractLeft (Q := (0 : QuadraticForm R M)) φ (ExteriorAlgebra.map (LinearMap.fst R M R)
        (contractLeft (Q := (0 : QuadraticForm R (M × R))) (LinearMap.snd R M R) z)) =
      -ExteriorAlgebra.map (LinearMap.fst R M R)
        (contractLeft (Q := (0 : QuadraticForm R (M × R))) (LinearMap.snd R M R)
          (contractLeft (Q := (0 : QuadraticForm R (M × R)))
            (φ.coprod (LinearMap.toSpanSingleton R R x)) z)) := by
  have hD := ExteriorAlgebra.map_inl_map_fst_add_ι_inr_mul_contractLeft_snd
    (contractLeft (Q := (0 : QuadraticForm R (M × R))) (LinearMap.snd R M R) z)
  rw [contractLeft_contractLeft, map_zero, map_zero, mul_zero, add_zero] at hD
  have hFI : Function.LeftInverse (ExteriorAlgebra.map (LinearMap.fst R M R))
      (ExteriorAlgebra.map (LinearMap.inl R M R)) :=
    ExteriorAlgebra.leftInverse_map_iff.2 fun _ ↦ rfl
  rw [← hFI (contractLeft _ _), ← contractLeft_coprod_map_inl φ x, hD, contractLeft_comm, map_neg]

/-- The `⋀ M`-component of the Koszul differential of `K(φ, x)`: writing `z = a + e ∧ b`, it is
`d a + x b`. -/
private theorem map_fst_koszulDifferential_coprod (k : ℕ) (z : ⋀[R]^(k + 1) (M × R)) :
    exteriorPower.map k (LinearMap.fst R M R)
        (koszulDifferential (φ.coprod (LinearMap.toSpanSingleton R R x)) k z) =
      koszulDifferential φ k (exteriorPower.map (k + 1) (LinearMap.fst R M R) z) +
        x • exteriorPower.map k (LinearMap.fst R M R)
          (koszulDifferential (LinearMap.snd R M R) k z) :=
  Subtype.ext <| by
    simp only [exteriorPower.coe_map, coe_koszulDifferential_apply, Submodule.coe_add,
      Submodule.coe_smul, map_fst_contractLeft_coprod]

/-- Writing a cycle `z` of `K(φ, x)` of degree `k + 1` as `a + e ∧ b`, if `b` is a boundary of
`K(φ)` and `K(φ)` is exact at `⋀ᵏ⁺¹ M`, then `z` is a boundary. -/
private theorem mem_range_koszulDifferential_coprod (k : ℕ)
    (hex : Function.Exact (koszulDifferential φ (k + 1)) (koszulDifferential φ k))
    (z : ⋀[R]^(k + 1) (M × R))
    (hz : koszulDifferential (φ.coprod (LinearMap.toSpanSingleton R R x)) k z = 0)
    (hb : exteriorPower.map k (LinearMap.fst R M R)
      (koszulDifferential (LinearMap.snd R M R) k z) ∈ LinearMap.range (koszulDifferential φ k)) :
    z ∈ LinearMap.range
      (koszulDifferential (φ.coprod (LinearMap.toSpanSingleton R R x)) (k + 1)) := by
  obtain ⟨c, hc⟩ := hb
  obtain ⟨u, hu⟩ := (hex (exteriorPower.map (k + 1) (LinearMap.fst R M R) z + x • c)).1 (by
    rw [map_add, map_smul, hc, ← map_fst_koszulDifferential_coprod, hz, map_zero])
  refine ⟨exteriorPower.map (k + 2) (LinearMap.inl R M R) u -
    ExteriorAlgebra.wedgeLeft (LinearMap.inr R M R 1) (k + 1)
      (exteriorPower.map (k + 1) (LinearMap.inl R M R) c), Subtype.ext ?_⟩
  have hu' := congrArg Subtype.val hu
  have hc' := congrArg Subtype.val hc
  simp only [coe_koszulDifferential_apply, exteriorPower.coe_map, Submodule.coe_add,
    Submodule.coe_smul] at hu' hc'
  simp only [coe_koszulDifferential_apply, Submodule.coe_sub, exteriorPower.coe_map,
    ExteriorAlgebra.coe_wedgeLeft_apply, map_sub, contractLeft_coprod_map_inl,
    contractLeft_coprod_ι_inr_mul, hu', hc', map_add, map_smul]
  conv_rhs => rw [← ExteriorAlgebra.map_inl_map_fst_add_ι_inr_mul_contractLeft_snd
    (z : ExteriorAlgebra R (M × R))]
  abel

/-- **Adjoining an element preserves higher acyclicity.** If the Koszul complex `K(φ)` is exact
at `⋀ᵏ⁺² M` and at `⋀ᵏ⁺¹ M`, then for every `x : R` the Koszul complex `K(φ, x)` of the functional
`(m, r) ↦ φ(m) + r x` on `M × R` is exact at `⋀ᵏ⁺² (M × R)`. -/
theorem exact_koszulDifferential_coprod_succ (k : ℕ)
    (h₁ : Function.Exact (koszulDifferential φ (k + 2)) (koszulDifferential φ (k + 1)))
    (h₀ : Function.Exact (koszulDifferential φ (k + 1)) (koszulDifferential φ k)) :
    Function.Exact (koszulDifferential (φ.coprod (LinearMap.toSpanSingleton R R x)) (k + 2))
      (koszulDifferential (φ.coprod (LinearMap.toSpanSingleton R R x)) (k + 1)) := by
  refine fun z ↦ ⟨fun hz ↦ mem_range_koszulDifferential_coprod φ x (k + 1) h₁ z hz ((h₀ _).1 ?_),
    ?_⟩
  · have hz' := congrArg Subtype.val hz
    simp only [coe_koszulDifferential_apply, ZeroMemClass.coe_zero] at hz'
    refine Subtype.ext ?_
    simp only [coe_koszulDifferential_apply, exteriorPower.coe_map,
      contractLeft_map_fst_contractLeft_snd φ x, hz', map_zero, neg_zero, ZeroMemClass.coe_zero]
  · rintro ⟨y, rfl⟩
    exact koszulDifferential_koszulDifferential _ _ y

/-- **Adjoining a nonzerodivisor preserves acyclicity in degree one.** If the Koszul complex
`K(φ)` is exact at `⋀¹ M` and `x` is a nonzerodivisor on `R ⧸ φ(M) ≃ H₀(K(φ))`, then the Koszul
complex `K(φ, x)` of the functional `(m, r) ↦ φ(m) + r x` on `M × R` is exact at `⋀¹ (M × R)`. -/
theorem exact_koszulDifferential_coprod_zero (hx : IsSMulRegular (R ⧸ LinearMap.range φ) x)
    (h₀ : Function.Exact (koszulDifferential φ 1) (koszulDifferential φ 0)) :
    Function.Exact (koszulDifferential (φ.coprod (LinearMap.toSpanSingleton R R x)) 1)
      (koszulDifferential (φ.coprod (LinearMap.toSpanSingleton R R x)) 0) := by
  refine fun z ↦ ⟨fun hz ↦ mem_range_koszulDifferential_coprod φ x 0 h₀ z hz ?_, ?_⟩
  · set b := exteriorPower.map 0 (LinearMap.fst R M R)
      (koszulDifferential (LinearMap.snd R M R) 0 z)
    have hxb : x • b ∈ LinearMap.range (koszulDifferential φ 0) :=
      ⟨-exteriorPower.map 1 (LinearMap.fst R M R) z, by
        rw [map_neg, neg_eq_iff_add_eq_zero, ← map_fst_koszulDifferential_coprod, hz, map_zero]⟩
    have hrange := map_zeroEquiv_range_koszulDifferential_zero φ
    have h₁ : exteriorPower.zeroEquiv R M b ∈ LinearMap.range φ := by
      refine (isSMulRegular_on_quot_iff_lsmul_comap_le _ _).1 hx ?_
      rw [Submodule.mem_comap, LinearMap.lsmul_apply, ← map_smul, ← hrange]
      exact Submodule.mem_map_of_mem hxb
    rw [← hrange] at h₁
    obtain ⟨y, hy, hyb⟩ := h₁
    rwa [← (exteriorPower.zeroEquiv R M).injective hyb]
  · rintro ⟨y, rfl⟩
    exact koszulDifferential_koszulDifferential _ _ y

end Adjoin

namespace koszulComplex

/-- The Koszul complex `K(φ)` is exact at `⋀ᵏ⁺¹ M`, i.e. `Hₖ₊₁(K(φ)) = 0`, exactly when the
Koszul differentials `⋀ᵏ⁺² M → ⋀ᵏ⁺¹ M → ⋀ᵏ M` are exact. -/
theorem exactAt_succ_iff (φ : Module.Dual R M) (k : ℕ) :
    (koszulComplex φ).ExactAt (k + 1) ↔
      Function.Exact (koszulDifferential φ (k + 1)) (koszulDifferential φ k) := by
  rw [HomologicalComplex.exactAt_iff' _ (k + 2) (k + 1) k (by simp) (by simp),
    ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
  simp only [HomologicalComplex.shortComplexFunctor'_obj_f,
    HomologicalComplex.shortComplexFunctor'_obj_g, koszulComplex_d]
  -- `ModuleCat.Hom.hom (ModuleCat.ofHom f)` is `f`; `ModuleCat.hom_ofHom` does not rewrite here
  -- because the terms of `koszulComplex φ` are only definitionally the exterior powers.
  rfl

/-- **The Koszul complex of a weakly regular sequence is acyclic in positive degrees**: if
`x = (x₀, …, xₙ₋₁)` is a weakly regular sequence in `R`, then `Hₖ₊₁(K(x)) = 0` for every `k`.
With `homologyZeroEquivSpan`, the complex of finite free modules `K(x)` resolves
`R ⧸ (x₀, …, xₙ₋₁)`. -/
theorem exactAt_of_isWeaklyRegular {n : ℕ} (x : Fin n → R)
    (hx : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn x)) (k : ℕ) :
    (koszulComplex (Fintype.linearCombination R x)).ExactAt (k + 1) := by
  rw [exactAt_succ_iff]
  induction n generalizing k with
  | zero =>
    intro z
    obtain rfl : z = 0 := by
      rcases subsingleton_or_nontrivial R with _ | _
      · exact (Module.subsingleton R _).elim z 0
      · exact exteriorPower.eq_zero_of_finrank_lt _
          (by rw [Module.finrank_zero_of_subsingleton]; omega) z
    exact ⟨fun _ ↦ ⟨0, map_zero _⟩, fun _ ↦ map_zero _⟩
  | succ n ih =>
    rw [List.ofFn_succ', List.concat_eq_append, RingTheory.Sequence.isWeaklyRegular_append_iff,
      RingTheory.Sequence.isWeaklyRegular_singleton_iff] at hx
    obtain ⟨hx₁, hx₂⟩ := hx
    set x' : Fin n → R := fun i ↦ x i.castSucc
    have hrange : (Ideal.ofList (List.ofFn x') • ⊤ : Submodule R R) =
        LinearMap.range (Fintype.linearCombination R x') := by
      rw [Fintype.range_linearCombination, smul_eq_mul, Ideal.mul_top, Ideal.ofList]
      congr 1
      ext r
      simp [List.mem_ofFn]
    rw [hrange] at hx₂
    have hexact : ∀ k, Function.Exact
        (koszulDifferential ((Fintype.linearCombination R x').coprod
          (LinearMap.toSpanSingleton R R (x (Fin.last n)))) (k + 1))
        (koszulDifferential ((Fintype.linearCombination R x').coprod
          (LinearMap.toSpanSingleton R R (x (Fin.last n)))) k)
    | 0 => exact_koszulDifferential_coprod_zero _ _ hx₂ (ih x' hx₁ 0)
    | k + 1 => exact_koszulDifferential_coprod_succ _ _ k (ih x' hx₁ (k + 1)) (ih x' hx₁ k)
    refine exact_koszulDifferential_of_retract
      ((LinearMap.pi fun i : Fin n ↦ LinearMap.proj i.castSucc).prod
        (LinearMap.proj (Fin.last n)))
      (LinearMap.pi fun i : Fin (n + 1) ↦ Fin.lastCases (LinearMap.snd R (Fin n → R) R)
        (fun j ↦ LinearMap.proj j ∘ₗ LinearMap.fst R (Fin n → R) R) i) ?_ ?_ k (hexact k)
    · refine LinearMap.ext fun v ↦ funext fun i ↦ ?_
      refine Fin.lastCases ?_ (fun j ↦ ?_) i <;> simp
    · ext v
      · simp [Fintype.linearCombination_apply, Fin.sum_univ_castSucc, x']
      · simp [Fintype.linearCombination_apply, Fin.sum_univ_castSucc]

end koszulComplex

end TauCeti
