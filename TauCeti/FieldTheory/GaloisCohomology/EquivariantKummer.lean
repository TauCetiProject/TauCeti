/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Rep.Res
public import TauCeti.Algebra.Group.PowerClassGroup.QuotSMulTop
public import TauCeti.Algebra.Module.ZMod.SMulCommClass
public import TauCeti.Data.ZMod.TrivialAction
public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.FiniteExtension
public import TauCeti.FieldTheory.GaloisCohomology.Kummer
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Conjugation
public import TauCeti.RepresentationTheory.Homological.ContCohomology.H1.ZMod
public import TauCeti.RepresentationTheory.QuotSMulTop
public import TauCeti.RepresentationTheory.RankOneTwist
public import TauCeti.RepresentationTheory.RestrictScalars
public import TauCeti.RepresentationTheory.TorsionBy
public import TauCeti.RingTheory.RootsOfUnity.Basic
public import TauCeti.RingTheory.RootsOfUnity.ZMod

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

Finally, for `L/K` normal, the file packages the three actions used in equivariant Kummer theory
at the finite Galois layer as `ZMod n`-linear representations of `Gal(L/K)`: the natural action on
power classes, the quotient of the action on `μₙ` when `N` acts trivially, and the quotient of the
conjugation action on `H¹(N, ℤ/n)`. These constructions do not require `L/K` to be finite. The
latter two actions are evaluated on restrictions of absolute Galois elements by
`kummerCoeffFiniteRepresentation_restrictNormalHom` and
`kummerH1FiniteRepresentation_restrictNormalHom`. Removing the cyclotomic twist then gives
**equivariant Kummer theory**: when `σ(L)` contains the `n`th roots of unity,

```text
kummerH1FiniteRepresentationEquiv σ n hn hN : H¹(N, ℤ/n) ≃ Hom(μₙ, ℤ/n) ⊗ Lˣ ⧸ (Lˣ)ⁿ
```

is an isomorphism of `ZMod n`-representations of `Gal(L/K)`, so natural in the `K`-automorphisms
of `L`.

## Main definitions

* `TauCeti.subgroupKummerCocycle`: the cocycle `h ↦ h α / α` on a subgroup fixing `αⁿ`.
* `TauCeti.fixingSubgroupKummerEquiv`: the Kummer isomorphism `Lˣ ⧸ (Lˣ)ⁿ ≃ H¹(N, μₙ)`.
* `TauCeti.fixingSubgroupKummerEquivOfTrivial`: the Kummer isomorphism `Lˣ ⧸ (Lˣ)ⁿ ≃ H¹(N, M)`
  with trivial coefficients `M ≃ μₙ`, when `σ(L)` contains the `n`th roots of unity.
* `TauCeti.powerClassFiniteRep`: the natural representation of `Gal(L/K)` on `Lˣ ⧸ (Lˣ)ⁿ`.
* `TauCeti.quotSMulTopUnitsPowerClassRepresentationEquiv`: the identification of the reduction
  `Lˣ ⧸ nLˣ` with `Lˣ ⧸ (Lˣ)ⁿ` respects the action of `Gal(L/K)`; it sends the class of `x` to
  its power class (`TauCeti.quotSMulTopUnitsPowerClassRepresentationEquiv_mk`).
* `TauCeti.kummerCoeffFiniteRep`: the roots-of-unity representation of `Gal(L/K)`.
* `TauCeti.kummerH1FiniteRep`: the conjugation representation of `Gal(L/K)` on `H¹(N, ℤ/n)`.
* `TauCeti.kummerH1FiniteRepresentationEquiv`: equivariant Kummer theory,
  `H¹(N, ℤ/n) ≃ Hom(μₙ, ℤ/n) ⊗ Lˣ ⧸ (Lˣ)ⁿ` as representations of `Gal(L/K)`.
* `TauCeti.torsionByUnitsEquivKummerCoeff`: when `σ(L)` contains the `n`th roots of unity, `σ`
  identifies the `n`-torsion `μₙ(L)` of `Lˣ` with `μₙ` as representations of `Gal(L/K)`.

## Main results

* `TauCeti.fixingSubgroupKummerEquiv_ofMul_mk`: the Kummer class of `b` is the class of
  `h ↦ h α / α` for every `n`th root `α` of `σ b`.
* `TauCeti.smul_fixingSubgroupKummerEquiv`: the Kummer isomorphism intertwines conjugation by
  `g ∈ G_K` with the action of the automorphism of `L` that `g` induces.
* `TauCeti.nsmul_smul_fixingSubgroupKummerEquivOfTrivial`: with trivial coefficients the same
  holds up to the cyclotomic twist.
* `TauCeti.dualTensorHom_kummerH1FiniteRepresentationEquiv`: equivariant Kummer theory sends the
  Kummer class of `x` to `ξ ↦ log ξ • x`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (6.2.1), and the
  proof of (7.3.1).
* J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., I, proof of Theorem 2.8.
-/

public section

noncomputable section

namespace TauCeti

open ContCohomology

section KummerIsomorphism

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

end KummerIsomorphism

/-! ## Finite-layer representations -/

universe u v

-- Adapted from the Tau Ceti lookahead branch
-- `lookahead/ClassFieldTheory/kummer-equiv-mixed-equivariant` (split 2).

/-! ### Power classes as a `ZMod`-module -/

/-- The `n`th power classes, written additively, form a `ZMod n`-module. -/
instance instModuleZModPowerClassQuotient {L : Type*} [Field L] (n : ℕ) :
    Module (ZMod n) (Additive (powerClassQuotient Lˣ n)) :=
  AddCommGroup.zmodModule fun x ↦ by
    induction x using Additive.rec with | ofMul x => ?_
    induction x using QuotientGroup.induction_on with | H a => ?_
    apply Additive.toMul.injective
    rw [toMul_nsmul, toMul_zero, toMul_ofMul, ← QuotientGroup.mk_pow,
      QuotientGroup.eq_one_iff]
    exact (mem_powerSubgroup_iff n).2 ⟨a, rfl⟩

variable {K : Type u} [Field K] {L : Type v} [Field L] [Algebra K L]

/-- The action of `Gal(L/K)` on `n`th power classes, induced functorially by its action on
`Lˣ`. -/
def powerClassRepresentation (n : ℕ) :
    Representation (ZMod n) Gal(L/K) (Additive (powerClassQuotient Lˣ n)) where
  toFun tau := AddMonoidHom.toZModLinearMap n
    (MonoidHom.toAdditive (powerClassMap n (Units.map (tau : L →* L))))
  map_one' := by
    have hmap : Units.map ((1 : Gal(L/K)) : L →* L) = MonoidHom.id Lˣ := by
      ext a
      simp
    ext x
    -- Expose the additive map hidden by the representation and `ZMod`-linear-map wrappers.
    change MonoidHom.toAdditive (powerClassMap n (Units.map ((1 : Gal(L/K)) : L →* L))) x = x
    rw [hmap, powerClassMap_id]
    rfl
  map_mul' tau upsilon := by
    have hmap : Units.map ((tau * upsilon : Gal(L/K)) : L →* L) =
        (Units.map (tau : L →* L)).comp (Units.map (upsilon : L →* L)) := by
      ext a
      rfl
    ext x
    -- Expose the additive map hidden by the representation and `ZMod`-linear-map wrappers.
    change MonoidHom.toAdditive
      (powerClassMap n (Units.map ((tau * upsilon : Gal(L/K)) : L →* L))) x = _
    rw [hmap, powerClassMap_comp]
    rfl

/-- The `ZMod n[Gal(L/K)]`-representation on the `n`th power classes of `L`. -/
@[expose] def powerClassFiniteRep (n : ℕ) : Rep (ZMod n) Gal(L/K) :=
  Rep.of (powerClassRepresentation (K := K) (L := L) n)

/-- The action of a `K`-automorphism on the power-class representation is the map induced on
units. -/
@[simp]
theorem powerClassRepresentation_apply (n : ℕ) (tau : Gal(L/K))
    (x : Additive (powerClassQuotient Lˣ n)) :
    powerClassRepresentation (K := K) (L := L) n tau x =
      MonoidHom.toAdditive (powerClassMap n (Units.map (tau : L →* L))) x := by
  rw [powerClassRepresentation]
  rfl

/-- The natural identification of additive reduction with power classes is equivariant for the
action of `Gal(L/K)`. -/
def quotSMulTopUnitsPowerClassRepresentationEquiv (n : ℕ) :
    ((Representation.ofDistribMulAction ℤ Gal(L/K) (Additive Lˣ)).quotSMulTop
      (n : ℤ)).Equiv
        (powerClassRepresentation (K := K) (L := L) n).restrictScalarsInt where
  toLinearEquiv := (quotSMulTopPowerClassEquiv n).toIntLinearEquiv
  isIntertwining' tau := by
    refine LinearMap.ext fun x ↦ ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, Representation.quotSMulTop_apply,
      Representation.restrictScalarsInt_apply, powerClassRepresentation_apply]
    -- On `Additive Lˣ`, the action of `tau` is the map induced by `Units.map tau`.
    exact quotSMulTopPowerClassEquiv_map n (Units.map (tau : L →* L)) x

/-- The equivariant reduction/power-class identification sends the class of `x` to its power
class. -/
@[simp]
theorem quotSMulTopUnitsPowerClassRepresentationEquiv_mk (n : ℕ) (x : Additive Lˣ) :
    quotSMulTopUnitsPowerClassRepresentationEquiv (K := K) n (Submodule.Quotient.mk x) =
      Additive.ofMul (powerClassHom Lˣ n x.toMul) :=
  -- The underlying linear equivalence is `quotSMulTopPowerClassEquiv n`, read `ℤ`-linearly.
  quotSMulTopPowerClassEquiv_mk n x

/-! ### The roots of unity of `L` -/

section RootsOfUnity

variable (sigma : L →ₐ[K] SeparableClosure K) (n : ℕ)

/-- An `n`-torsion element of `Lˣ`, written additively, read as an `n`th root of unity of `Kˢ`
through the embedding `σ`. -/
private def torsionByUnitsToKummerCoeff :
    Submodule.torsionBy ℤ (Additive Lˣ) (n : ℤ) →+ KummerCoeff K n :=
  (restrictRootsOfUnity sigma n).toAdditive.comp (torsionByUnitsEquivRootsOfUnity n).toAddMonoidHom

private theorem bijective_torsionByUnitsToKummerCoeff
    (hN : ∀ g : AbsoluteGaloisGroup K, g ∈ sigma.fieldRange.fixingSubgroup →
      ∀ xi : KummerCoeff K n, g • xi = xi) :
    Function.Bijective (torsionByUnitsToKummerCoeff sigma n) := by
  refine ⟨fun x y h ↦ ?_, fun xi ↦ ?_⟩
  · have h' := congrArg (fun z : KummerCoeff K n ↦ ((z.toMul : (SeparableClosure K)ˣ) :
      SeparableClosure K)) h
    simp only [torsionByUnitsToKummerCoeff, AddMonoidHom.coe_comp, Function.comp_apply,
      MonoidHom.toAdditive_apply_apply, toMul_ofMul, restrictRootsOfUnity_coe_apply,
      AddEquiv.coe_toAddMonoidHom, coe_torsionByUnitsEquivRootsOfUnity_apply] at h'
    exact Subtype.ext (Additive.toMul.injective (Units.ext (sigma.injective h')))
  · set ζ : SeparableClosure K := ((xi.toMul : (SeparableClosure K)ˣ) : SeparableClosure K)
    have hfix : ζ ∈ IntermediateField.fixedField sigma.fieldRange.fixingSubgroup := by
      rintro ⟨g, hg⟩
      have h := congrArg (fun z : KummerCoeff K n ↦ ((z.toMul : (SeparableClosure K)ˣ) :
        SeparableClosure K)) (hN g hg xi)
      simpa [AlgEquiv.smul_units_def] using h
    rw [InfiniteGalois.fixedField_fixingSubgroup] at hfix
    obtain ⟨y, hy⟩ := hfix
    have hy0 : y ≠ 0 := by
      rintro rfl
      exact xi.toMul.1.ne_zero (by simp [ζ, ← hy])
    have hyn : Units.mk0 y hy0 ^ n = 1 := by
      apply Units.ext
      apply sigma.injective
      have := congrArg (fun u : (SeparableClosure K)ˣ ↦ (u : SeparableClosure K))
        ((mem_rootsOfUnity n _).1 xi.toMul.2)
      simpa [ζ, ← hy] using this
    refine ⟨⟨Additive.ofMul (Units.mk0 y hy0), (Submodule.mem_torsionBy_iff _ _).2 ?_⟩, ?_⟩
    · apply Additive.toMul.injective
      simpa [natCast_zsmul] using hyn
    · apply Additive.toMul.injective
      exact Subtype.ext (Units.ext (by simpa [torsionByUnitsToKummerCoeff] using hy))

end RootsOfUnity

/-! ### Quotients of the absolute Galois action -/

section FiniteGalois

variable [Normal K L]
  (sigma : L →ₐ[K] SeparableClosure K) (n : ℕ)

/-- The roots-of-unity representation of `Gal(L/K)`, obtained by factoring the absolute Galois
action through the subgroup fixing `sigma(L)`. -/
def kummerCoeffFiniteRepresentation
    (hN : ∀ g : AbsoluteGaloisGroup K, g ∈ sigma.fieldRange.fixingSubgroup →
      ∀ xi : KummerCoeff K n, g • xi = xi) :
    Representation (ZMod n) Gal(L/K) (KummerCoeff K n) := by
  let rho : Representation (ZMod n) (AbsoluteGaloisGroup K) (KummerCoeff K n) :=
    Representation.ofDistribMulAction (ZMod n) (AbsoluteGaloisGroup K) (KummerCoeff K n)
  let _ : Representation.IsTrivial
      (rho.comp sigma.fieldRange.fixingSubgroup.subtype) :=
    ⟨fun g ↦ by
      apply LinearMap.ext
      intro xi
      exact hN g g.2 xi⟩
  exact (rho.ofQuotient sigma.fieldRange.fixingSubgroup).comp
    (quotientFixingSubgroupFieldRangeEquiv K L sigma).symm.toMonoidHom

/-- The roots-of-unity representation as an object of `Rep`. -/
def kummerCoeffFiniteRep
    (hN : ∀ g : AbsoluteGaloisGroup K, g ∈ sigma.fieldRange.fixingSubgroup →
      ∀ xi : KummerCoeff K n, g • xi = xi) :
    Rep (ZMod n) Gal(L/K) :=
  Rep.of (kummerCoeffFiniteRepresentation sigma n hN)

/-- The quotient roots-of-unity action, evaluated at the restriction of an absolute Galois
element, is its original action. -/
@[simp]
theorem kummerCoeffFiniteRepresentation_restrictNormalHom
    (hN : ∀ g : AbsoluteGaloisGroup K, g ∈ sigma.fieldRange.fixingSubgroup →
      ∀ xi : KummerCoeff K n, g • xi = xi)
    (g : AbsoluteGaloisGroup K) (xi : KummerCoeff K n) :
    kummerCoeffFiniteRepresentation sigma n hN (sigma.restrictNormalHom g) xi = g • xi := by
  let rho : Representation (ZMod n) (AbsoluteGaloisGroup K) (KummerCoeff K n) :=
    Representation.ofDistribMulAction (ZMod n) (AbsoluteGaloisGroup K) (KummerCoeff K n)
  let _ : Representation.IsTrivial
      (rho.comp sigma.fieldRange.fixingSubgroup.subtype) :=
    ⟨fun h ↦ by
      apply LinearMap.ext
      intro zeta
      exact hN h h.2 zeta⟩
  unfold kummerCoeffFiniteRepresentation
  rw [← quotientFixingSubgroupFieldRangeEquiv_mk K L sigma g]
  rw [MonoidHom.comp_apply]
  have hq : (quotientFixingSubgroupFieldRangeEquiv K L sigma).symm.toMonoidHom
      ((quotientFixingSubgroupFieldRangeEquiv K L sigma)
        (g : AbsoluteGaloisGroup K ⧸ sigma.fieldRange.fixingSubgroup)) = g :=
    (quotientFixingSubgroupFieldRangeEquiv K L sigma).symm_apply_apply _
  rw [hq, Representation.ofQuotient_coe_apply]
  rfl

/-- **The roots of unity of `L` are those of `Kˢ`.** If the subgroup of `G_K` fixing `σ(L)`
fixes the `n`th roots of unity of `Kˢ`, then `σ` identifies the `n`-torsion `μ_n(L)` of `Lˣ`
with `μ_n(Kˢ)`, as representations of `Gal(L/K)`: an `n`th root of unity fixed by that subgroup
lies in `σ(L)` by infinite Galois theory (`InfiniteGalois.fixedField_fixingSubgroup`). -/
def torsionByUnitsEquivKummerCoeff
    (hN : ∀ g : AbsoluteGaloisGroup K, g ∈ sigma.fieldRange.fixingSubgroup →
      ∀ xi : KummerCoeff K n, g • xi = xi) :
    ((Representation.ofDistribMulAction ℤ Gal(L/K) (Additive Lˣ)).torsionBy n).Equiv
      (kummerCoeffFiniteRepresentation sigma n hN).restrictScalarsInt := by
  refine .mk (AddEquiv.ofBijective _ (bijective_torsionByUnitsToKummerCoeff sigma n hN)
    ).toIntLinearEquiv fun tau ↦ LinearMap.ext fun x ↦ ?_
  obtain ⟨g, rfl⟩ := sigma.restrictNormalHom_surjective tau
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, AddEquiv.coe_toIntLinearEquiv,
    AddEquiv.ofBijective_apply, Representation.restrictScalarsInt_apply]
  rw [kummerCoeffFiniteRepresentation_restrictNormalHom]
  apply Additive.toMul.injective
  ext
  simp [torsionByUnitsToKummerCoeff, restrictRootsOfUnity_coe_apply, AlgEquiv.smul_units_def]

/-- `torsionByUnitsEquivKummerCoeff` sends an `n`-torsion unit `x` of `L` to `σ x`. -/
@[simp]
theorem coe_torsionByUnitsEquivKummerCoeff_apply
    (hN : ∀ g : AbsoluteGaloisGroup K, g ∈ sigma.fieldRange.fixingSubgroup →
      ∀ xi : KummerCoeff K n, g • xi = xi)
    (x : Submodule.torsionBy ℤ (Additive Lˣ) (n : ℤ)) :
    (((torsionByUnitsEquivKummerCoeff sigma n hN x).toMul : (SeparableClosure K)ˣ) :
      SeparableClosure K) = sigma (x.1.toMul : L) := by
  simp [torsionByUnitsEquivKummerCoeff, torsionByUnitsToKummerCoeff]

/-- The absolute Galois group acts trivially on the constant coefficient module. -/
local instance : DistribMulAction (AbsoluteGaloisGroup K) (ZMod n) :=
  trivialZModAction n (AbsoluteGaloisGroup K)

local instance : ContinuousSMul (AbsoluteGaloisGroup K) (ZMod n) :=
  ⟨continuous_snd⟩

/-- The conjugation action of the absolute Galois group on first cohomology, as a linear
representation over `ZMod n`. -/
def kummerH1AbsoluteRepresentation :
    Representation (ZMod n) (AbsoluteGaloisGroup K)
      (H1 sigma.fieldRange.fixingSubgroup (ZMod n)) where
  toFun g := AddMonoidHom.toZModLinearMap n
    (ContCohomology.explicitConj1 sigma.fieldRange.fixingSubgroup g)
  map_one' := by
    ext x
    simp
  map_mul' g h := by
    ext x
    simp

/-- The conjugation representation on `H¹` is trivial on the subgroup acting by inner
automorphisms. -/
instance instIsTrivialKummerH1AbsoluteRepresentation : Representation.IsTrivial
    ((kummerH1AbsoluteRepresentation sigma n).comp
      sigma.fieldRange.fixingSubgroup.subtype) where
  out g := by
    ext x
    exact ContCohomology.smul_eq_self_of_mem sigma.fieldRange.fixingSubgroup g x

/-- The `Gal(L/K)`-representation on `H¹(Gal(Kˢ/sigma(L)), ZMod n)` induced by conjugation. -/
def kummerH1FiniteRepresentation :
    Representation (ZMod n) Gal(L/K)
      (H1 sigma.fieldRange.fixingSubgroup (ZMod n)) :=
  ((kummerH1AbsoluteRepresentation sigma n).ofQuotient
      sigma.fieldRange.fixingSubgroup).comp
    (quotientFixingSubgroupFieldRangeEquiv K L sigma).symm.toMonoidHom

/-- The finite-layer first-cohomology representation as an object of `Rep`. -/
def kummerH1FiniteRep : Rep (ZMod n) Gal(L/K) :=
  Rep.of (kummerH1FiniteRepresentation sigma n)

/-- The finite-layer cohomology action, evaluated at the restriction of an absolute Galois
element, is conjugation by that element. -/
@[simp]
theorem kummerH1FiniteRepresentation_restrictNormalHom (g : AbsoluteGaloisGroup K)
    (x : H1 sigma.fieldRange.fixingSubgroup (ZMod n)) :
    kummerH1FiniteRepresentation sigma n (sigma.restrictNormalHom g) x = g • x := by
  unfold kummerH1FiniteRepresentation
  rw [← quotientFixingSubgroupFieldRangeEquiv_mk K L sigma g]
  rw [MonoidHom.comp_apply]
  have hq : (quotientFixingSubgroupFieldRangeEquiv K L sigma).symm.toMonoidHom
      ((quotientFixingSubgroupFieldRangeEquiv K L sigma)
        (g : AbsoluteGaloisGroup K ⧸ sigma.fieldRange.fixingSubgroup)) = g :=
    (quotientFixingSubgroupFieldRangeEquiv K L sigma).symm_apply_apply _
  rw [hq, Representation.ofQuotient_coe_apply]
  rfl

/-! ### Equivariant Kummer theory -/

/-- The Kummer isomorphism with coefficients `ℤ/n` intertwines the actions of `Gal(L/K)` up to
the character of the roots-of-unity representation: the hypothesis of
`Representation.rankOneTwistEquiv` for `kummerH1FiniteRepresentationEquiv`. -/
private theorem rankOneCharacter_smul_kummerH1FiniteRepresentation (hn : IsUnit (n : K))
    (hN : ∀ g : AbsoluteGaloisGroup K, g ∈ sigma.fieldRange.fixingSubgroup →
      ∀ xi : KummerCoeff K n, g • xi = xi)
    (tau : Gal(L/K)) (x : Additive (powerClassQuotient Lˣ n)) :
    Representation.rankOneCharacter (kummerCoeffFiniteRepresentation sigma n hN)
        ((kummerCoeffAddEquivZMod hn).toLinearEquiv (ZMod.map_smul _)) tau •
        kummerH1FiniteRepresentation sigma n tau
          (fixingSubgroupKummerEquivOfTrivial sigma hn (kummerCoeffAddEquivZMod hn)
            (fun _ _ ↦ rfl) hN x) =
      fixingSubgroupKummerEquivOfTrivial sigma hn (kummerCoeffAddEquivZMod hn) (fun _ _ ↦ rfl) hN
        (powerClassRepresentation n tau x) := by
  have : NeZero n := ⟨by rintro rfl; simp at hn⟩
  obtain ⟨g, rfl⟩ := sigma.restrictNormalHom_surjective tau
  -- `g` acts on `μₙ` as the `c`th power map, for `c` the value of the character at `g`.
  generalize hc : Representation.rankOneCharacter (kummerCoeffFiniteRepresentation sigma n hN)
    ((kummerCoeffAddEquivZMod hn).toLinearEquiv (ZMod.map_smul _)) (sigma.restrictNormalHom g) = c
  have hk (xi : KummerCoeff K n) : g • xi = c.val • xi := by
    rw [← kummerCoeffFiniteRepresentation_restrictNormalHom sigma n hN g xi,
      Representation.rankOneCharacter_smul _
        ((kummerCoeffAddEquivZMod hn).toLinearEquiv (ZMod.map_smul _)), hc,
      ← Nat.cast_smul_eq_nsmul (ZMod n), ZMod.natCast_zmod_val]
  rw [kummerH1FiniteRepresentation_restrictNormalHom, powerClassRepresentation_apply,
    ← ZMod.natCast_zmod_val c, Nat.cast_smul_eq_nsmul]
  -- The twisted equivariance reads the automorphism of `L` through `L →ₐ[K] L`.
  have hmap : ((sigma.restrictNormalHom g : L →ₐ[K] L) : L →* L) = sigma.restrictNormalHom g :=
    MonoidHom.ext fun _ ↦ rfl
  refine (nsmul_smul_fixingSubgroupKummerEquivOfTrivial sigma hn (kummerCoeffAddEquivZMod hn)
    (fun _ _ ↦ rfl) hN g (sigma.restrictNormalHom g : L →ₐ[K] L)
    (sigma.restrictNormalHom_commutes g) c.val hk x).trans ?_
  exact congrArg _ (congrArg (fun f ↦ MonoidHom.toAdditive (powerClassMap n (Units.map f)) x) hmap)

-- Adapted from the Tau Ceti lookahead branch
-- `lookahead/ClassFieldTheory/kummer-equiv-mixed-equivariant` (split 3).
/-- **Equivariant Kummer theory with constant coefficients.** Let `L/K` be normal, `n` invertible
in `K`, and let the subgroup `N` of `G_K` fixing `sigma(L)` act trivially on `μₙ`, that is,
`sigma(L)` contains the `n`th roots of unity. Then `H¹(N, ℤ/n)` is isomorphic to
`Hom(μₙ, ℤ/n) ⊗ Lˣ ⧸ (Lˣ)ⁿ` as a `ZMod n`-representation of `Gal(L/K)`, where `Gal(L/K)` acts on
`H¹(N, ℤ/n)` by conjugation, on `μₙ` through `G_K`, and on power classes through its action on
`Lˣ`. Being an isomorphism of representations, it is natural in the `K`-automorphisms of `L`.

The underlying isomorphism is the Kummer isomorphism with trivial coefficients
`fixingSubgroupKummerEquivOfTrivial`, along `μₙ ≃ ℤ/n` (`kummerCoeffAddEquivZMod`), with its
cyclotomic twist removed by `Representation.rankOneTwistEquiv`; it sends the class of `x` to
`ξ ↦ log ξ • x` (`dualTensorHom_kummerH1FiniteRepresentationEquiv`). -/
def kummerH1FiniteRepresentationEquiv (hn : IsUnit (n : K))
    (hN : ∀ g : AbsoluteGaloisGroup K, g ∈ sigma.fieldRange.fixingSubgroup →
      ∀ xi : KummerCoeff K n, g • xi = xi) :
    (kummerH1FiniteRepresentation sigma n).Equiv
      ((kummerCoeffFiniteRepresentation sigma n hN).dual.tprod
        (powerClassRepresentation (K := K) (L := L) n)) :=
  Representation.rankOneTwistEquiv (kummerCoeffFiniteRepresentation sigma n hN)
    (powerClassRepresentation n) (kummerH1FiniteRepresentation sigma n)
    ((kummerCoeffAddEquivZMod hn).toLinearEquiv (ZMod.map_smul _))
    ((fixingSubgroupKummerEquivOfTrivial sigma hn (kummerCoeffAddEquivZMod hn) (fun _ _ ↦ rfl)
      hN).toLinearEquiv (ZMod.map_smul _))
    fun tau x ↦ by
      rw [AddEquiv.coe_toLinearEquiv]
      exact rankOneCharacter_smul_kummerH1FiniteRepresentation sigma n hn hN tau x

/-- **The equivariant Kummer isomorphism on Kummer classes.** Under
`kummerH1FiniteRepresentationEquiv`, the Kummer class of a power class `x` corresponds to the
homomorphism `μₙ → Lˣ ⧸ (Lˣ)ⁿ` sending `ξ` to `log ξ • x`, with `log : μₙ ≃ ℤ/n` the
identification `kummerCoeffAddEquivZMod`. -/
@[simp]
theorem dualTensorHom_kummerH1FiniteRepresentationEquiv (hn : IsUnit (n : K))
    (hN : ∀ g : AbsoluteGaloisGroup K, g ∈ sigma.fieldRange.fixingSubgroup →
      ∀ xi : KummerCoeff K n, g • xi = xi)
    (x : Additive (powerClassQuotient Lˣ n)) (xi : KummerCoeff K n) :
    dualTensorHom (ZMod n) (KummerCoeff K n) (Additive (powerClassQuotient Lˣ n))
        (kummerH1FiniteRepresentationEquiv sigma n hn hN
          (fixingSubgroupKummerEquivOfTrivial sigma hn (kummerCoeffAddEquivZMod hn)
            (fun _ _ ↦ rfl) hN x)) xi =
      kummerCoeffAddEquivZMod hn xi • x := by
  rw [kummerH1FiniteRepresentationEquiv, Representation.dualTensorHom_rankOneTwistEquiv,
    LinearEquiv.rankOneHomEquiv_apply_apply]
  simp

end FiniteGalois

end TauCeti
