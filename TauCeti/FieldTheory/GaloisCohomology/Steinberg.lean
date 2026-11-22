/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.GaloisCohomology.Kummer
public import TauCeti.RepresentationTheory.Homological.ContCohomology.ProjectionFormula
import TauCeti.FieldTheory.Kummer.Norm

/-!
# The Steinberg relation for cup products of Kummer classes

Let `K` be a field and `n` a natural number invertible in `K`. Cupping the Kummer classes
`(a), (b) ∈ H¹(G_K, μₙ)` along an equivariant biadditive pairing `μ : μₙ × μₙ → P` into a discrete
`G_K`-module gives a class `(a) ⌣ (b) ∈ H²(G_K, P)`. This file proves the **Steinberg relation**:
`(a) ⌣ (b) = 0` whenever `a + b = 1`. It holds for every such pairing, in particular for the
pairing `μₙ × μₙ → μₙ` attached to a primitive `n`th root of unity of `K`, through which the local
Hilbert symbol is defined.

The proof is Tate's, via `Submonoid.mem_of_add_eq_one_of_normUnits_mem`. For a finite extension
`L/K` in which `a` is an `n`th power, the Kummer class of a norm is a corestriction
(`TauCeti.kummerCor_kummerMap`), so by the projection formula
`TauCeti.ContCohomology.explicitCup_projection11`

```text
(a) ⌣ (N_{L/K} c) = (a) ⌣ cor (c) = cor (res (a) ⌣ (c)) = 0,
```

because the restriction of `(a)` to `G_L` is the Kummer class of an `n`th power. Factoring `Xⁿ - a`
into monic irreducible polynomials writes `b = 1 - a` as a product of such norms.

Everything is stated on the explicit low-degree cohomology of `G_K = Gal(Kˢ/K)`, where the Kummer
map `TauCeti.kummerMap` and the projection formula live.

## Main results

* `TauCeti.explicitRes1_kummerMap_eq_zero`: the Kummer class of `a` restricts to zero on the
  subgroup fixing the image of an extension in which `a` is an `n`th power.
* `TauCeti.explicitCup11_kummerMap_normUnits_eq_zero`: `(a) ⌣ (N_{L/K} c) = 0` for a finite
  extension `L/K` in which `a` is an `n`th power.
* `TauCeti.explicitCup11_kummerMap_eq_zero_of_add_eq_one`: the Steinberg relation
  `(a) ⌣ (b) = 0` for `a + b = 1`.

## References

* J. Tate, *Relations between K₂ and Galois cohomology*, Invent. Math. 36 (1976), 257–274.
* J.-P. Serre, *Local Fields*, GTM 67, Chapter XIV, §2.
-/

public section

noncomputable section

namespace TauCeti

open ContCohomology

universe u v

variable {K : Type u} [Field K] {n : ℕ}

/-- **The Kummer class of `a` dies where `a` becomes an `n`th power**: if `a = βⁿ` in an
extension `L` of `K`, then the Kummer class of `a` restricts to zero on the subgroup of `G_K`
fixing the image of any `K`-embedding `σ : L →ₐ[K] Kˢ`. It is represented there by the cocycle
`g ↦ g (σ β) / σ β`, which is identically `1`. -/
theorem explicitRes1_kummerMap_eq_zero (hn : IsUnit (n : K)) {L : Type v} [Field L]
    [Algebra K L] (σ : L →ₐ[K] SeparableClosure K) {a : Kˣ} {β : Lˣ}
    (hβ : β ^ n = Units.map (algebraMap K L).toMonoidHom a) :
    explicitRes1 (AbsoluteGaloisGroup K) (KummerCoeff K n) σ.fieldRange.fixingSubgroup
      (kummerMap K n hn a).toAdd = 0 := by
  have hα : Units.map σ.toRingHom.toMonoidHom β ^ n =
      Units.map (algebraMap K (SeparableClosure K)).toMonoidHom a := by
    rw [← map_pow, hβ]
    ext
    simp
  rw [kummerMap_eq_kummerCocycleClass hn hα, kummerCocycleClass_def, QuotientAddGroup.mk'_apply,
    explicitRes1_mk, QuotientAddGroup.eq_zero_iff]
  convert AddSubgroup.zero_mem _
  refine Subtype.ext (funext fun g => ?_)
  rw [cocyclesMap1_apply, AddMonoidHom.id_apply]
  refine Additive.toMul.injective (Subtype.ext ?_)
  simpa using mul_inv_eq_one.2 (Units.ext ((mem_fixingSubgroup_iff _).1 g.property _ ⟨(β : L),
      rfl⟩))

section Cup

variable {P : Type*} [AddCommGroup P] [TopologicalSpace P] [DiscreteTopology P]
  [DistribMulAction (AbsoluteGaloisGroup K) P] [ContinuousSMul (AbsoluteGaloisGroup K) P]
  (μ : KummerCoeff K n →+ KummerCoeff K n →+ P)
  (hμ : ∀ (g : AbsoluteGaloisGroup K) (x y : KummerCoeff K n), μ (g • x) (g • y) = g • μ x y)

/-- **The Kummer class of `a` cups to zero with every norm from an extension in which `a` is an
`n`th power**: if `a = βⁿ` in a finite extension `L/K`, then `(a) ⌣ (N_{L/K} c) = 0` for every
`c ∈ Lˣ`. The Kummer class of the norm is the corestriction of the Kummer class of `c`, and by the
projection formula `(a) ⌣ cor (c) = cor (res (a) ⌣ (c))`, where `res (a) = 0` by
`TauCeti.explicitRes1_kummerMap_eq_zero`. -/
theorem explicitCup11_kummerMap_normUnits_eq_zero (hn : IsUnit (n : K)) {L : Type v} [Field L]
    [Algebra K L] [FiniteDimensional K L] (σ : L →ₐ[K] SeparableClosure K) {a : Kˣ} {β : Lˣ}
    (hβ : β ^ n = Units.map (algebraMap K L).toMonoidHom a) (c : Lˣ) :
    explicitCup11 (AbsoluteGaloisGroup K) (KummerCoeff K n) (KummerCoeff K n) P μ
        continuous_of_discreteTopology hμ (kummerMap K n hn a).toAdd
        (kummerMap K n hn (Algebra.normUnits K c)).toAdd = 0 := by
  have hnL : IsUnit (n : L) := by simpa using hn.map (algebraMap K L)
  rw [← kummerCor_kummerMap K n L σ hnL c, toAdd_kummerCor,
    ← explicitCup_projection11 _ _ _ _ _ (isOpen_fixingSubgroup_fieldRange K L σ) μ
      continuous_of_discreteTopology hμ,
    explicitRes1_kummerMap_eq_zero hn σ hβ, map_zero, AddMonoidHom.zero_apply, map_zero]

/-- **The Steinberg relation** (Tate): for `n` invertible in `K` and units `a`, `b` of `K` with
`a + b = 1`, the cup product `(a) ⌣ (b) ∈ H²(G_K, P)` of their Kummer classes vanishes, for every
equivariant biadditive pairing `μ : μₙ × μₙ → P`. -/
theorem explicitCup11_kummerMap_eq_zero_of_add_eq_one (hn : IsUnit (n : K)) {a b : Kˣ}
    (hab : (a : K) + b = 1) :
    explicitCup11 (AbsoluteGaloisGroup K) (KummerCoeff K n) (KummerCoeff K n) P μ
        continuous_of_discreteTopology hμ (kummerMap K n hn a).toAdd
        (kummerMap K n hn b).toAdd = 0 := by
  let S : Submonoid Kˣ :=
    { carrier := {c : Kˣ |
        explicitCup11 (AbsoluteGaloisGroup K) (KummerCoeff K n) (KummerCoeff K n) P μ
          continuous_of_discreteTopology hμ (kummerMap K n hn a).toAdd
          (kummerMap K n hn c).toAdd = 0}
      one_mem' := by simp
      mul_mem' := fun {c d} hc hd ↦ by
        simp only [Set.mem_ofPred_eq, map_mul, toAdd_mul, map_add] at hc hd ⊢
        rw [hc, hd, add_zero] }
  exact S.mem_of_add_eq_one_of_normUnits_mem hn.ne_zero (add_comm (a : K) b ▸ hab)
    fun L _ _ _ _ β hβ _ c ↦
      explicitCup11_kummerMap_normUnits_eq_zero μ hμ hn IsSepClosed.lift hβ c

end Cup

end TauCeti
