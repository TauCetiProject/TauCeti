/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.GaloisCohomology.Kummer
public import TauCeti.RepresentationTheory.Homological.ContCohomology.ProjectionFormula
public import TauCeti.RingTheory.Polynomial.Resultant.AdjoinRoot

/-!
# The Steinberg relation for cup products of Kummer classes

Let `K` be a field and `n` a natural number invertible in `K`. Cupping the Kummer classes
`(a), (b) ∈ H¹(G_K, μₙ)` along an equivariant biadditive pairing `μ : μₙ × μₙ → P` into a discrete
`G_K`-module gives a class `(a) ⌣ (b) ∈ H²(G_K, P)`. This file proves the **Steinberg relation**:
`(a) ⌣ (b) = 0` whenever `a + b = 1`. It holds for every such pairing, in particular for the
pairing `μₙ × μₙ → μₙ` attached to a primitive `n`th root of unity of `K`, through which the local
Hilbert symbol is defined.

The proof is Tate's. Factor `Xⁿ - a` over `K` into monic irreducible polynomials `f`. In the field
`L_f = K[X]/(f)` the root `θ_f` of `f` satisfies `θ_fⁿ = a`, so `a` becomes an `n`th power in
`L_f`, while `f(1) = N_{L_f/K}(1 - θ_f)`. Hence `b = 1 - a = ∏_f N_{L_f/K}(1 - θ_f)` is a product
of norms. For a finite extension `L/K` in which `a` is an `n`th power, the Kummer class of a norm is
a corestriction (`TauCeti.kummerCor_kummerMap`), so by the projection formula
`TauCeti.ContCohomology.explicitCup_projection11`

```text
(a) ⌣ (N_{L/K} c) = (a) ⌣ cor (c) = cor (res (a) ⌣ (c)) = 0,
```

because the restriction of `(a)` to `G_L` is the Kummer class of an `n`th power.

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

open ContCohomology Polynomial

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
  simpa using mul_inv_eq_one.2 (Units.ext ((mem_fixingSubgroup_iff _).1 g.2 _ ⟨(β : L), rfl⟩))

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

/-- **One monic irreducible factor of `Xⁿ - a`**: if `f` is a monic irreducible factor of
`Xⁿ - a` and `a ≠ 1`, then `f(1)` is a unit `c` of `K` with `(a) ⌣ (c) = 0`. Indeed
`f(1) = N_{L/K}(1 - θ)` for the root `θ` of `f` in `L = K[X]/(f)`, where `a = θⁿ`, so this is
`TauCeti.explicitCup11_kummerMap_normUnits_eq_zero`. -/
private theorem exists_eval_one_explicitCup11_kummerMap_eq_zero (hn : IsUnit (n : K)) {a : Kˣ}
    (ha : (a : K) ≠ 1) {f : K[X]} (hirr : Irreducible f) (hmonic : f.Monic)
    (hdvd : f ∣ X ^ n - C (a : K)) :
    ∃ c : Kˣ, (c : K) = f.eval 1 ∧
      explicitCup11 (AbsoluteGaloisGroup K) (KummerCoeff K n) (KummerCoeff K n) P μ
        continuous_of_discreteTopology hμ (kummerMap K n hn a).toAdd
        (kummerMap K n hn c).toAdd = 0 := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  have := Fact.mk hirr
  have : FiniteDimensional K (AdjoinRoot f) := (AdjoinRoot.powerBasis hirr.ne_zero).finite
  -- `f` divides the separable `Xⁿ - a`, so it has a root in `Kˢ`: a `K`-embedding of `K[X]/(f)`
  obtain ⟨x, hx⟩ := IsSepClosed.exists_aeval_eq_zero (SeparableClosure K) f
    (degree_pos_of_irreducible hirr).ne'
    ((separable_X_pow_sub_C _ hn.ne_zero a.ne_zero).of_dvd hdvd)
  have hθ : AdjoinRoot.root f ^ n = AdjoinRoot.of f a := by
    have h := AdjoinRoot.mk_eq_zero.2 hdvd
    rw [← AdjoinRoot.aeval_eq, map_sub, map_pow, aeval_X, aeval_C] at h
    exact sub_eq_zero.1 h
  have hθ0 : AdjoinRoot.root f ≠ 0 := fun h => by
    rw [h, zero_pow hn0, eq_comm, map_eq_zero_iff _ (AdjoinRoot.of f).injective] at hθ
    exact a.ne_zero hθ
  have hθ1 : 1 - AdjoinRoot.root f ≠ 0 := fun h => by
    rw [← sub_eq_zero.1 h, one_pow, eq_comm, map_eq_one_iff _ (AdjoinRoot.of f).injective] at hθ
    exact ha hθ
  refine ⟨Algebra.normUnits K (Units.mk0 _ hθ1), ?_,
    explicitCup11_kummerMap_normUnits_eq_zero μ hμ hn (AdjoinRoot.liftAlgHom f (Algebra.ofId K _) x
      (by rw [Algebra.toRingHom_ofId, ← aeval_def]; exact hx))
      (β := Units.mk0 _ hθ0) (Units.ext (by simpa using hθ)) _⟩
  rw [Algebra.coe_normUnits, Units.val_mk0, ← map_one (AdjoinRoot.of f),
    AdjoinRoot.norm_algebraMap_sub_root hmonic]

/-- **The Steinberg relation** (Tate): for `n` invertible in `K` and units `a`, `b` of `K` with
`a + b = 1`, the cup product `(a) ⌣ (b) ∈ H²(G_K, P)` of their Kummer classes vanishes, for every
equivariant biadditive pairing `μ : μₙ × μₙ → P`. -/
theorem explicitCup11_kummerMap_eq_zero_of_add_eq_one (hn : IsUnit (n : K)) {a b : Kˣ}
    (hab : (a : K) + b = 1) :
    explicitCup11 (AbsoluteGaloisGroup K) (KummerCoeff K n) (KummerCoeff K n) P μ
        continuous_of_discreteTopology hμ (kummerMap K n hn a).toAdd
        (kummerMap K n hn b).toAdd = 0 := by
  classical
  set cup : Kˣ → _ := fun c => explicitCup11 (AbsoluteGaloisGroup K) (KummerCoeff K n)
    (KummerCoeff K n) P μ continuous_of_discreteTopology hμ (kummerMap K n hn a).toAdd
      (kummerMap K n hn c).toAdd with hcup
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  have ha : (a : K) ≠ 1 := fun ha => b.ne_zero (by linear_combination hab - ha)
  set p : K[X] := X ^ n - C (a : K) with hp
  have hpmonic : p.Monic := monic_X_pow_sub_C _ hn0
  -- `p(1) = 1 - a = b` is the product of the values `f(1)` over the monic irreducible factors `f`
  -- of `p`, and each of them is a unit `c` with `(a) ⌣ (c) = 0`
  obtain ⟨c, hc, hc0⟩ : ∃ c : Kˣ, (c : K) = p.eval 1 ∧ cup c = 0 := by
    have hprod := leadingCoeff_mul_prod_normalizedFactors p
    rw [hpmonic.leadingCoeff, C_1, one_mul] at hprod
    rw [← hprod, eval_multiset_prod]
    refine Multiset.prod_induction (fun y => ∃ c : Kˣ, (c : K) = y ∧ cup c = 0) _ ?_
      ⟨1, Units.val_one, by simp [hcup]⟩ ?_
    · rintro _ _ ⟨c, rfl, hc⟩ ⟨d, rfl, hd⟩
      refine ⟨c * d, Units.val_mul c d, ?_⟩
      simp only [hcup, map_mul, toAdd_mul, map_add] at hc hd ⊢
      rw [hc, hd, add_zero]
    · intro y hy
      obtain ⟨f, hf, rfl⟩ := Multiset.mem_map.1 hy
      obtain ⟨hirr, hmonic, hdvd⟩ := (Polynomial.mem_normalizedFactors_iff hpmonic.ne_zero).1 hf
      exact exists_eval_one_explicitCup11_kummerMap_eq_zero μ hμ hn ha hirr hmonic hdvd
  have hcb : c = b := Units.ext (by
    rw [hc, hp, eval_sub, eval_pow, eval_X, eval_C, one_pow, ← hab, add_sub_cancel_left])
  exact hcb ▸ hc0

end Cup

end TauCeti
