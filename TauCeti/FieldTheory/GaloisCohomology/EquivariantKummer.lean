/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.GaloisCohomology.Kummer
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Conjugation

/-!
# The Kummer isomorphism on a fixing subgroup, and its Galois equivariance

Let `K` be a field, `Kˢ` a separable closure, `G_K = AbsoluteGaloisGroup K`, `n` a natural number
invertible in `K`, and `σ : L →ₐ[K] Kˢ` an embedding of an extension `L/K`. The subgroup
`N = Gal(Kˢ/σ(L))` of `G_K` fixing `σ(L)` is a copy of `G_L`, and the Kummer isomorphism of `L`
read on it is

```text
fixingSubgroupKummerEquiv σ hn : Lˣ ⧸ (Lˣ)ⁿ ≃ H¹(N, μₙ),
```

with `μₙ = μₙ(Kˢ)` the Kummer coefficient module of `K`. It sends the power class of `b ∈ Lˣ` to
the class of the cocycle `h ↦ h α / α`, for any `n`th root `α ∈ Kˢ` of `σ b`
(`fixingSubgroupKummerEquiv_ofMul_mk`); the cocycle is `subgroupKummerCocycle`.

When `N` is normal, `G_K` acts on `H¹(N, μₙ)` by conjugation on `N` together with its action on
`μₙ` (`TauCeti.ContCohomology.explicitConj1`), and the subgroup `N` acts trivially, so this is an
action of `G_K ⧸ N`. It acts on `Lˣ ⧸ (Lˣ)ⁿ` through the `K`-automorphisms of `L`: `g ∈ G_K`
acts as the automorphism `τ` with `σ ∘ τ = g ∘ σ`. The Kummer isomorphism is **equivariant** for
these two actions (`smul_fixingSubgroupKummerEquiv`). This is the Galois-module structure on
`H¹(L, μₙ)` that is used to compute with Kummer theory over a finite Galois extension `L/K`.

If moreover `σ(L)` contains the `n`th roots of unity, that is, `N` acts trivially on `μₙ`, then an
identification `e : μₙ ≃ M` with a module `M` on which `G_K` acts trivially, such as `ℤ/n`, gives
the Kummer isomorphism with trivial coefficients

```text
Ψ = fixingSubgroupKummerEquivOfTrivial σ hn e htriv hN : Lˣ ⧸ (Lˣ)ⁿ ≃ H¹(N, M).
```

It is equivariant only up to a twist: `G_K` acts on `μₙ` through the cyclotomic character, and
if `g` acts on `μₙ` as the `k`th power map then `k • (g • Ψ x) = Ψ (τ x)`
(`nsmul_smul_fixingSubgroupKummerEquivOfTrivial`). So, as modules over `G_K ⧸ N`, which is
`Gal(L/K)` for `L/K` Galois, `H¹(N, M) ≅ μₙ^{⊗ -1} ⊗ Lˣ ⧸ (Lˣ)ⁿ`.

## Main definitions

* `TauCeti.subgroupKummerCocycle`: the cocycle `h ↦ h α / α` on a subgroup fixing `αⁿ`.
* `TauCeti.fixingSubgroupKummerEquiv`: the Kummer isomorphism `Lˣ ⧸ (Lˣ)ⁿ ≃ H¹(N, μₙ)`.
* `TauCeti.fixingSubgroupKummerEquivOfTrivial`: the Kummer isomorphism `Lˣ ⧸ (Lˣ)ⁿ ≃ H¹(N, M)`
  with trivial coefficients `M ≃ μₙ`, when `σ(L)` contains the `n`th roots of unity.

## Main results

* `TauCeti.fixingSubgroupKummerEquiv_ofMul_mk`: the Kummer class of `b` is the class of
  `h ↦ h α / α` for every `n`th root `α` of `σ b`.
* `TauCeti.smul_fixingSubgroupKummerEquiv`: the Kummer isomorphism intertwines conjugation by
  `g ∈ G_K` with the action of the automorphism of `L` that `g` induces.
* `TauCeti.nsmul_smul_fixingSubgroupKummerEquivOfTrivial`: with trivial coefficients the same
  holds up to the cyclotomic twist.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (6.2.1), and the
  proof of (7.3.1).
* J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., I, proof of Theorem 2.8.
-/

public section

noncomputable section

namespace TauCeti

open ContCohomology

variable {K : Type*} [Field K] {n : ℕ} {L : Type*} [Field L] [Algebra K L]

/-! ### The Kummer cocycle on a subgroup fixing an `n`th power -/

section Cocycle

variable {N : Subgroup (AbsoluteGaloisGroup K)} {α : (SeparableClosure K)ˣ}

/-- The ratio `h α / α` is an `n`th root of unity when `h` fixes `αⁿ`. -/
theorem smul_mul_inv_mem_rootsOfUnity_of_smul_pow_eq (hα : ∀ h ∈ N, h • α ^ n = α ^ n) (h : N) :
    (h : AbsoluteGaloisGroup K) • α * α⁻¹ ∈ rootsOfUnity n (SeparableClosure K) := by
  rw [mem_rootsOfUnity, mul_pow, ← smul_pow', inv_pow, hα _ h.2, mul_inv_cancel]

/-- The function `h ↦ h α / α` on a subgroup `N` of `G_K` fixing `αⁿ`, with values in `μₙ`; the
underlying function of `subgroupKummerCocycle`. -/
private def subgroupKummerRatio (hα : ∀ h ∈ N, h • α ^ n = α ^ n) : N → KummerCoeff K n :=
  fun h => Additive.ofMul ⟨(h : AbsoluteGaloisGroup K) • α * α⁻¹,
    smul_mul_inv_mem_rootsOfUnity_of_smul_pow_eq hα h⟩

/-- The coefficient inclusion of `h α / α` is the coboundary ratio `h • α - α` in the units of
`Kˢ`. -/
private theorem kummerCoeffIncl_subgroupKummerRatio (hα : ∀ h ∈ N, h • α ^ n = α ^ n) (h : N) :
    kummerCoeffIncl K n (subgroupKummerRatio hα h) =
      d0 N (UnitsCoeff K) (Additive.ofMul α) h :=
  Additive.toMul.injective <| by
    rw [toMul_kummerCoeffIncl, d0_apply, toMul_sub, Subgroup.smul_def, Additive.toMul_smul,
      toMul_ofMul, div_eq_mul_inv]
    rfl

/-- **The Kummer cocycle on a subgroup** `N` of `G_K` fixing `αⁿ`: the continuous `1`-cocycle
`h ↦ h α / α` with values in `μₙ`, the counterpart for `N` of `TauCeti.kummerCocycle`. On the
subgroup fixing `σ(L)` and for `αⁿ = σ b`, its class is the Kummer class of `b ∈ Lˣ`
(`fixingSubgroupKummerEquiv_ofMul_mk`). -/
def subgroupKummerCocycle (hα : ∀ h ∈ N, h • α ^ n = α ^ n) : Z1 N (KummerCoeff K n) :=
  ⟨subgroupKummerRatio hα, mem_Z1_iff.2
    ⟨continuous_of_injective_comp (kummerCoeffIncl_injective K n) <| by
      simpa only [Function.comp_def, kummerCoeffIncl_subgroupKummerRatio] using
        continuous_d0_apply (G := N) (Additive.ofMul α : UnitsCoeff K),
    fun g h => kummerCoeffIncl_injective K n <| by
      rw [map_add, Subgroup.smul_def, kummerCoeffIncl_equivariant, ← Subgroup.smul_def,
        kummerCoeffIncl_subgroupKummerRatio, kummerCoeffIncl_subgroupKummerRatio,
        kummerCoeffIncl_subgroupKummerRatio, d0_apply, d0_apply, d0_apply, smul_sub, smul_smul]
      abel⟩⟩

/-- The value of `subgroupKummerCocycle` at `h` is the ratio `h α / α`. -/
@[simp]
theorem toMul_subgroupKummerCocycle (hα : ∀ h ∈ N, h • α ^ n = α ^ n) (h : N) :
    (((subgroupKummerCocycle hα : N → KummerCoeff K n) h).toMul : (SeparableClosure K)ˣ) =
      (h : AbsoluteGaloisGroup K) • α * α⁻¹ :=
  (rfl)

end Cocycle

/-! ### The Kummer isomorphism on the subgroup fixing `σ(L)` -/

section FixingSubgroup

variable {σ : L →ₐ[K] SeparableClosure K} {b : Lˣ} {α : (SeparableClosure K)ˣ}

/-- An element fixing `σ(L)` fixes every `n`th root of `σ b`, raised to the `n`th power. -/
theorem smul_pow_eq_of_mem_fixingSubgroup (hα : (α : SeparableClosure K) ^ n = σ b) :
    ∀ h : AbsoluteGaloisGroup K, h ∈ σ.fieldRange.fixingSubgroup → h • α ^ n = α ^ n :=
  fun h hh => Units.ext <| by
  rw [AlgEquiv.smul_units_def, Units.coe_map, MonoidHom.coe_ofClass, Units.val_pow_eq_pow_val,
    hα]
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hh _ ⟨b, rfl⟩

/-- The `n`th root `α ∈ Kˢ` of `σ b`, carried to `Lˢ` by the identification of separable closures,
is an `n`th root of `b`. -/
private theorem units_map_separableClosureRingEquiv_symm_pow_eq
    (hα : (α : SeparableClosure K) ^ n = σ b) :
    Units.map (separableClosureRingEquiv K L σ).symm.toMonoidHom α ^ n =
      Units.map (algebraMap L (SeparableClosure L)).toMonoidHom b := by
  ext
  simp [← map_pow, hα]

/-- The cocycle of the Kummer class of `b ∈ Lˣ`, transported from `G_L` to the subgroup fixing
`σ(L)`, is `h ↦ h α / α` for the image `α ∈ Kˢ` of the chosen root. -/
private theorem cocyclesMap1_kummerCocycle (hα : (α : SeparableClosure K) ^ n = σ b) :
    cocyclesMap1 (AbsoluteGaloisGroup L) (KummerCoeff L n) ↥σ.fieldRange.fixingSubgroup
      (KummerCoeff K n)
      ((absoluteGaloisGroupEquivFixingSubgroup K L σ).symm :
        ↥σ.fieldRange.fixingSubgroup →ₜ* AbsoluteGaloisGroup L)
      (kummerCoeffMapSymm K n L σ) continuous_of_discreteTopology
      (kummerCoeffMapSymm_smul K n L σ)
      ⟨kummerCocycle (units_map_separableClosureRingEquiv_symm_pow_eq hα),
        kummerCocycle_mem_Z1 _⟩ =
      subgroupKummerCocycle (N := σ.fieldRange.fixingSubgroup)
        (smul_pow_eq_of_mem_fixingSubgroup hα) := by
  refine Subtype.ext (funext fun h => ?_)
  rw [cocyclesMap1_apply]
  exact Additive.toMul.injective (Subtype.ext (Units.ext (by simp)))

end FixingSubgroup

variable (σ : L →ₐ[K] SeparableClosure K)

/-- **The Kummer isomorphism of `L` on the subgroup of `G_K` fixing `σ(L)`**,
`Lˣ ⧸ (Lˣ)ⁿ ≃ H¹(Gal(Kˢ/σ(L)), μₙ(Kˢ))`, for `n` invertible in `K`: the Kummer isomorphism
`TauCeti.kummerIso` of `L`, transported along `absoluteGaloisGroupEquivFixingSubgroup K L σ` and
the identification of roots of unity `kummerCoeffMapSymm K n L σ`. The class of `b` is
represented by `h ↦ h α / α` for any `n`th root `α` of `σ b`
(`fixingSubgroupKummerEquiv_ofMul_mk`). -/
def fixingSubgroupKummerEquiv (hn : IsUnit (n : K)) :
    Additive (powerClassQuotient Lˣ n) ≃+
      H1 σ.fieldRange.fixingSubgroup (KummerCoeff K n) :=
  (MulEquiv.toAdditiveLeft (kummerIso L n (by simpa using hn.map (algebraMap K L)))).trans
    (explicitMap1Equiv (AbsoluteGaloisGroup L) (KummerCoeff L n) ↥σ.fieldRange.fixingSubgroup
      (KummerCoeff K n) (absoluteGaloisGroupEquivFixingSubgroup K L σ).symm
      (AddMonoidHom.toAddEquiv (kummerCoeffMapSymm K n L σ) (kummerCoeffMap K n L σ)
        (AddMonoidHom.ext (kummerCoeffMap_kummerCoeffMapSymm K n L σ))
        (AddMonoidHom.ext (kummerCoeffMapSymm_kummerCoeffMap K n L σ)))
      continuous_of_discreteTopology continuous_of_discreteTopology
      (kummerCoeffMapSymm_smul K n L σ))

/-- `fixingSubgroupKummerEquiv` is the Kummer isomorphism of `L` followed by the transport to the
subgroup fixing `σ(L)`. -/
theorem fixingSubgroupKummerEquiv_apply (hn : IsUnit (n : K))
    (x : Additive (powerClassQuotient Lˣ n)) :
    fixingSubgroupKummerEquiv σ hn x =
      explicitMap1 (AbsoluteGaloisGroup L) (KummerCoeff L n) ↥σ.fieldRange.fixingSubgroup
        (KummerCoeff K n)
        ((absoluteGaloisGroupEquivFixingSubgroup K L σ).symm :
          ↥σ.fieldRange.fixingSubgroup →ₜ* AbsoluteGaloisGroup L)
        (kummerCoeffMapSymm K n L σ) continuous_of_discreteTopology
        (kummerCoeffMapSymm_smul K n L σ)
        (Multiplicative.toAdd (kummerIso L n (by simpa using hn.map (algebraMap K L)) x.toMul)) :=
  explicitMap1Equiv_apply _ _ _ _ _ _ _ _ _ _

variable {σ} in
/-- **The Kummer class on the subgroup fixing `σ(L)` is represented by `h ↦ h α / α`**, for every
`n`th root `α ∈ Kˢ` of `σ b`. -/
theorem fixingSubgroupKummerEquiv_ofMul_mk (hn : IsUnit (n : K)) {b : Lˣ}
    {α : (SeparableClosure K)ˣ} (hα : (α : SeparableClosure K) ^ n = σ b) :
    fixingSubgroupKummerEquiv σ hn (Additive.ofMul (b : powerClassQuotient Lˣ n)) =
      H1pi _ _ (subgroupKummerCocycle (N := σ.fieldRange.fixingSubgroup)
        (smul_pow_eq_of_mem_fixingSubgroup hα)) := by
  have hnL : IsUnit (n : L) := by simpa using hn.map (algebraMap K L)
  rw [fixingSubgroupKummerEquiv_apply, toMul_ofMul, kummerIso_mk,
    kummerMap_eq_kummerCocycleClass hnL (units_map_separableClosureRingEquiv_symm_pow_eq hα),
    kummerCocycleClass_def, H1pi, QuotientAddGroup.mk'_apply, QuotientAddGroup.mk'_apply,
    explicitMap1_mk, cocyclesMap1_kummerCocycle hα]

/-- **The Kummer isomorphism is Galois equivariant.** Let the subgroup `N` of `G_K` fixing `σ(L)`
be normal, so that `G_K` acts on `H¹(N, μₙ)` by conjugation. If `g ∈ G_K` and the
`K`-endomorphism `τ` of `L` satisfy `σ ∘ τ = g ∘ σ`, then conjugation by `g` corresponds under the
Kummer isomorphism to the map of power classes `Lˣ ⧸ (Lˣ)ⁿ → Lˣ ⧸ (Lˣ)ⁿ` induced by `τ`. -/
theorem smul_fixingSubgroupKummerEquiv [σ.fieldRange.fixingSubgroup.Normal] (hn : IsUnit (n : K))
    (g : AbsoluteGaloisGroup K) (τ : L →ₐ[K] L) (hτ : ∀ x, σ (τ x) = g (σ x))
    (x : Additive (powerClassQuotient Lˣ n)) :
    g • fixingSubgroupKummerEquiv σ hn x =
      fixingSubgroupKummerEquiv σ hn
        (MonoidHom.toAdditive (powerClassMap n (Units.map (τ : L →* L))) x) := by
  have hnL : IsUnit (n : L) := by simpa using hn.map (algebraMap K L)
  induction x using Additive.rec with | ofMul x => ?_
  induction x using QuotientGroup.induction_on with | H b => ?_
  -- An `n`th root `α ∈ Kˢ` of `σ b`, and its conjugate `g α`, an `n`th root of `σ (τ b)`.
  obtain ⟨β, hβ⟩ := exists_pow_eq_units_map hnL b
  set α := Units.map (separableClosureRingEquiv K L σ).toMonoidHom β
  have hα : (α : SeparableClosure K) ^ n = σ b := by
    rw [Units.coe_map, ← map_pow, ← Units.val_pow_eq_pow_val, hβ]
    simp
  have hgα : ((g • α : (SeparableClosure K)ˣ) : SeparableClosure K) ^ n =
      σ (Units.map (τ : L →* L) b : Lˣ) := by
    simp [← map_pow, hα, hτ]
  rw [MonoidHom.toAdditive_apply_apply, toMul_ofMul, powerClassMap_mk,
    fixingSubgroupKummerEquiv_ofMul_mk hn hα, fixingSubgroupKummerEquiv_ofMul_mk hn hgα, H1pi,
    QuotientAddGroup.mk'_apply, QuotientAddGroup.mk'_apply, smul_mk]
  refine congrArg _ (Subtype.ext (funext fun h => Additive.toMul.injective
    (Subtype.ext (Units.ext ?_))))
  rw [cocyclesMap1_apply]
  simp [mul_smul]

/-! ### Trivial coefficients and the cyclotomic twist -/

section Trivial

variable {M : Type*} [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  [DistribMulAction (AbsoluteGaloisGroup K) M]
  [ContinuousSMul (AbsoluteGaloisGroup K) M]

/-- **The Kummer isomorphism with trivial coefficients**, `Lˣ ⧸ (Lˣ)ⁿ ≃ H¹(N, M)` on the subgroup
`N` of `G_K` fixing `σ(L)`, when `N` acts trivially on `μₙ`, that is, when `σ(L)` contains the
`n`th roots of unity, and `e : μₙ ≃ M` identifies `μₙ` with a module on which `G_K` acts trivially:
`fixingSubgroupKummerEquiv` followed by the coefficient isomorphism induced by `e`, which is
`N`-equivariant because `N` acts trivially on both sides. -/
def fixingSubgroupKummerEquivOfTrivial (hn : IsUnit (n : K)) (e : KummerCoeff K n ≃+ M)
    (htriv : ∀ (g : AbsoluteGaloisGroup K) (m : M), g • m = m)
    (hN : ∀ h : AbsoluteGaloisGroup K, h ∈ σ.fieldRange.fixingSubgroup →
      ∀ ξ : KummerCoeff K n, h • ξ = ξ) :
    Additive (powerClassQuotient Lˣ n) ≃+ H1 σ.fieldRange.fixingSubgroup M :=
  (fixingSubgroupKummerEquiv σ hn).trans
    (explicitCoeff1Equiv σ.fieldRange.fixingSubgroup (KummerCoeff K n) e
      continuous_of_discreteTopology continuous_of_discreteTopology fun h ξ => by
        rw [Subgroup.smul_def, Subgroup.smul_def, hN _ h.2, htriv])

/-- `fixingSubgroupKummerEquivOfTrivial` is the Kummer isomorphism followed by the coefficient map
induced by `e`. -/
theorem fixingSubgroupKummerEquivOfTrivial_apply (hn : IsUnit (n : K)) (e : KummerCoeff K n ≃+ M)
    (htriv : ∀ (g : AbsoluteGaloisGroup K) (m : M), g • m = m)
    (hN : ∀ h : AbsoluteGaloisGroup K, h ∈ σ.fieldRange.fixingSubgroup →
      ∀ ξ : KummerCoeff K n, h • ξ = ξ)
    (x : Additive (powerClassQuotient Lˣ n)) :
    fixingSubgroupKummerEquivOfTrivial σ hn e htriv hN x =
      explicitCoeff1Equiv σ.fieldRange.fixingSubgroup (KummerCoeff K n) e
        continuous_of_discreteTopology continuous_of_discreteTopology
        (fun h ξ => by rw [Subgroup.smul_def, Subgroup.smul_def, hN _ h.2, htriv])
        (fixingSubgroupKummerEquiv σ hn x) :=
  (rfl)

/-- **The Kummer isomorphism with trivial coefficients is equivariant up to the cyclotomic
twist.** If `g ∈ G_K` acts on `μₙ` as the `k`th power map and the `K`-endomorphism `τ` of `L`
satisfies `σ ∘ τ = g ∘ σ`, then `k` times the conjugate by `g` of the class of `x` is the class of
`τ x`. As `k` is the value at `g` of the cyclotomic character modulo `n`, this identifies `H¹(N, M)`
with `μₙ^{⊗ -1} ⊗ Lˣ ⧸ (Lˣ)ⁿ` as a module over `G_K ⧸ N`. -/
theorem nsmul_smul_fixingSubgroupKummerEquivOfTrivial [σ.fieldRange.fixingSubgroup.Normal]
    (hn : IsUnit (n : K)) (e : KummerCoeff K n ≃+ M)
    (htriv : ∀ (g : AbsoluteGaloisGroup K) (m : M), g • m = m)
    (hN : ∀ h : AbsoluteGaloisGroup K, h ∈ σ.fieldRange.fixingSubgroup →
      ∀ ξ : KummerCoeff K n, h • ξ = ξ)
    (g : AbsoluteGaloisGroup K) (τ : L →ₐ[K] L) (hτ : ∀ x, σ (τ x) = g (σ x)) (k : ℕ)
    (hk : ∀ ξ : KummerCoeff K n, g • ξ = k • ξ) (x : Additive (powerClassQuotient Lˣ n)) :
    k • g • fixingSubgroupKummerEquivOfTrivial σ hn e htriv hN x =
      fixingSubgroupKummerEquivOfTrivial σ hn e htriv hN
        (MonoidHom.toAdditive (powerClassMap n (Units.map (τ : L →* L))) x) := by
  rw [fixingSubgroupKummerEquivOfTrivial_apply, fixingSubgroupKummerEquivOfTrivial_apply,
    ← smul_fixingSubgroupKummerEquiv σ hn g τ hτ, explicitCoeff1Equiv_apply,
    explicitCoeff1Equiv_apply]
  refine (explicitCoeff1_smul_of_map_smul _ _ _ g k (fun ξ => ?_) _).symm
  simp [hk, htriv]

end Trivial

end TauCeti
