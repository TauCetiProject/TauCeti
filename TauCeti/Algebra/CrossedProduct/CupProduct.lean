/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.CrossedProduct.Quaternion
public import TauCeti.Algebra.CrossedProduct.TwoTorsion
public import TauCeti.FieldTheory.GaloisCohomology.MuTwo.Cup
import TauCeti.Algebra.Group.Units.Basic
import TauCeti.FieldTheory.IntermediateField.Quadratic

/-!
# The quaternion symbol as a cup product

Let `K` be a field in which `2` is invertible. This file proves that the comparison
`TauCeti.brauerCohomologyEquiv K : Br(K) ≃ H²_cont(G_K, (Kˢ)ˣ)` sends the quaternion symbol
`[(a, b)]` to the image under `TauCeti.h2MuToUnits K` of the cup product `(a) ∪ (b)` of the
Kummer classes of `a` and `b` (`TauCeti.brauerCohomologyEquiv_quaternionClass`). Read through the
`2`-torsion comparison `TauCeti.brauer2EquivH2 K : Br(K)[2] ≃ H²_cont(G_K, 𝔽₂)`, this is the
classical identity `ι [(a, b)] = (a) ∪ (b)` (`TauCeti.brauer2EquivH2_quaternionClass`).

If `a` is a square, both sides vanish. Otherwise, choose square roots `α` of `a` and `β` of `b` in
`Kˢ`, and let `L = K(α)`, a quadratic Galois subextension of `Kˢ`. The computation has three steps.

* The quaternion algebra `(a, b)` is the crossed product of the quadratic cocycle of `b` over `L`
  (`TauCeti.BrauerGroup.crossedProductClass_quadratic`), so the comparison sends `[(a, b)]` to the
  inflation of that cocycle, `c(g, k) = b` if neither `g` nor `k` fixes `α`, and `1` otherwise
  (`TauCeti.brauerCohomologyEquiv_crossedProductClass`).
* On explicit cocycles, `(a)` and `(b)` are `χ_α(g) = [g α ≠ α]` and `χ_β(k) = [k β ≠ β]`, their
  cup product is `χ_α(g) χ_β(k)`, and `h2MuToUnits K` sends it to the class of
  `w(g, k) = (-1) ^ (χ_α(g) χ_β(k))`.
* The two cocycles differ by the coboundary of the continuous cochain `f(g) = (g β) ^ χ_α(g)`:
  `c = w · d f`. This is a direct check on the eight cases `g α = ± α`, `k α = ± α`, `k β = ± β`.

## Main results

* `TauCeti.TwoCocycle.inflateClass_quadratic_eq_h2MuToUnits_cup`: the cyclic class represented
  by the quadratic cocycle of `b` inflates to the image of `(a) ∪ (b)` in the multiplicative
  coefficients.
* `TauCeti.brauerCohomologyEquiv_quaternionClass`: the comparison sends `[(a, b)]` to
  `h2MuToUnits K ((a) ∪ (b))`.
* `TauCeti.brauer2EquivH2_quaternionClass`: the `2`-torsion comparison sends `[(a, b)]` to
  `(a) ∪ (b)`.

## References

* J.-P. Serre, *Local Fields*, Graduate Texts in Mathematics 67, Springer (1979), Chapter XIV,
  §2, Proposition 5.
* P. Gille and T. Szamuely, *Central Simple Algebras and Galois Cohomology* (2006), Proposition
  4.7.1.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory ContCohomology _root_.ContinuousCohomology _root_.IntermediateField

attribute [local instance] TopRep.distribMulAction

variable {K : Type} [Field K]

/-- The trivial `𝔽₂` coefficients are a discrete `G_K`-module. -/
local instance : ContinuousSMul (AbsoluteGaloisGroup K) (trivialF2 (AbsoluteGaloisGroup K)).V :=
  (isSmoothDiscrete_trivialF2 (AbsoluteGaloisGroup K)).continuousSMul

/-- The absolute Galois group is locally compact, being compact and Hausdorff. Instance search
does not find this within its default budget under the imports of this file, so it is assembled
here from the Krull topology being Hausdorff. -/
local instance : LocallyCompactSpace (AbsoluteGaloisGroup K) :=
  have : R1Space (AbsoluteGaloisGroup K) := @T2Space.r1Space _ _ krullTopology_t2
  have : WeaklyLocallyCompactSpace (AbsoluteGaloisGroup K) :=
    ⟨fun _ ↦ ⟨Set.univ, isCompact_univ, Filter.univ_mem⟩⟩
  WeaklyLocallyCompactSpace.locallyCompactSpace

/-! ### The cup product of Kummer classes on explicit cocycles -/

variable [Invertible (2 : K)]

variable (K) in
/-- The inverse of the coefficient dictionary `μ₂ ≃ 𝔽₂`, as a `G_K`-equivariant map. -/
private def trivialF2ToMu2 :
    (trivialF2 (AbsoluteGaloisGroup K)).V →+[AbsoluteGaloisGroup K] KummerCoeff K 2 :=
  { (kummerCoeffEquiv K).symm.toAddMonoidHom with
    map_smul' := fun g b ↦ by
      simp only [AddMonoidHom.toFun_eq_coe, AddEquiv.coe_toAddMonoidHom, MonoidHom.id_apply,
        mu2_smul_eq_self, TopRep.distribMulAction_smul, trivialF2_ρ_apply_apply] }

/-- `trivialF2ToMu2` is the inverse coefficient dictionary. -/
private theorem trivialF2ToMu2_apply (b : (trivialF2 (AbsoluteGaloisGroup K)).V) :
    trivialF2ToMu2 K b = (kummerCoeffEquiv K).symm b :=
  (rfl)

/-- The inverse of `kummerCoeffIsoTrivialF2`, read on the discrete module `𝔽₂`, is the coefficient
map of `trivialF2ToMu2`. -/
private theorem eqToHom_comp_kummerCoeffIsoTrivialF2_inv :
    eqToHom (ofDiscreteModule_trivialF2 (AbsoluteGaloisGroup K)) ≫
        (kummerCoeffIsoTrivialF2 K).inv =
      ofDiscreteModuleMap (trivialF2ToMu2 K).toAddMonoidHom.toIntLinearMap
        fun g m ↦ map_smul (trivialF2ToMu2 K) g m := by
  refine TopRep.hom_ext (DFunLike.ext _ _ fun (b : (trivialF2 (AbsoluteGaloisGroup K)).V) ↦ ?_)
  -- The goal is the composite read at a carrier, which no rewrite reaches: `TopRep.comp_apply` is
  -- stated at the carrier of a `TopRep` object, and the carrier of `ofDiscreteModule` is not
  -- syntactically the module. `change` exposes the composite, as in
  -- `TauCeti.kummerCoeffIsoTrivialF2_inv_apply`; the remaining goal is
  -- `ofDiscreteModuleMap_hom_apply`, stated at the unfolded carrier.
  change (kummerCoeffIsoTrivialF2 K).inv
    (eqToHom (ofDiscreteModule_trivialF2 (AbsoluteGaloisGroup K)) b) = _
  rw [eqToHom_ofDiscreteModule_trivialF2_apply, kummerCoeffIsoTrivialF2_inv_apply]
  rfl

/-- On an explicit class of `H²(G_K, 𝔽₂)`, `h2MuToUnits K` is the explicit coefficient map along
`𝔽₂ ≃ μ₂ ⊆ (Kˢ)ˣ`. -/
private theorem h2MuToUnits_explicitH2
    (z : H2 (AbsoluteGaloisGroup K) (trivialF2 (AbsoluteGaloisGroup K)).V) :
    (h2MuToUnits K).hom ((eqToHom (congrArg (continuousCohomology 2)
          (ofDiscreteModule_trivialF2 (AbsoluteGaloisGroup K)))).hom
        (explicitH2AddEquivContinuousCohomology _ _ z)) =
      explicitH2AddEquivContinuousCohomology _ _
        (explicitCoeff2 _ _ (kummerShortExact K 2 (isUnit_of_invertible _)).inclDistribMulActionHom
          continuous_of_discreteTopology
          (explicitCoeff2 _ _ (trivialF2ToMu2 K) continuous_of_discreteTopology z)) := by
  have hcomparison (x : H2 (AbsoluteGaloisGroup K) (KummerCoeff K 2)) :
      (h2KummerToUnits K 2).hom (explicitH2AddEquivContinuousCohomology _ _ x) =
        explicitH2AddEquivContinuousCohomology _ _
          (explicitCoeff2 _ _
            (kummerShortExact K 2 (isUnit_of_invertible _)).inclDistribMulActionHom
            continuous_of_discreteTopology x) := by
    simpa only [explicitCoeff2_eq_explicitMap2,
      DiscreteShortExact.coe_addMonoidHom_inclDistribMulActionHom, kummerShortExact_incl] using
      h2KummerToUnits_explicitH2AddEquivContinuousCohomology x
  rw [h2MuToUnits_def, ← TauCeti.ContinuousCohomology.coeffMap_eqToHom, ← hcomparison,
    ← explicitH2AddEquivContinuousCohomology_coeffMap, ← eqToHom_comp_kummerCoeffIsoTrivialF2_inv,
    TauCeti.ContinuousCohomology.coeffMap_comp]
  -- the two sides apply the same composite of coefficient maps, once as a composite morphism and
  -- once as two successive applications
  rfl

/-- The element `0` of `𝔽₂` goes to `1` in `(Kˢ)ˣ`, and the element `1` goes to `-1`. -/
private theorem toMul_kummerCoeffIncl_trivialF2ToMu2 (b : (trivialF2 (AbsoluteGaloisGroup K)).V) :
    (kummerCoeffIncl K 2 (trivialF2ToMu2 K b)).toMul =
      if trivialF2Equiv (AbsoluteGaloisGroup K) b = 0 then 1 else -1 := by
  rw [toMul_kummerCoeffIncl, trivialF2ToMu2_apply, kummerCoeffEquiv_symm_apply]
  generalize trivialF2Equiv (AbsoluteGaloisGroup K) b = v
  rcases (by decide : ∀ v : ZMod 2, v = 0 ∨ v = 1) v with rfl | rfl
  · rw [map_zero, toMul_zero, OneMemClass.coe_one, ite_eq_left_iff.2 fun h ↦ (h rfl).elim]
  · rw [← mu2EquivZMod2_apply_mu2NegOne (K := K), AddEquiv.symm_apply_apply, toMul_mu2NegOne,
      mu2EquivZMod2_apply_mu2NegOne, ite_eq_right_of_eq_false _ _ (eq_false one_ne_zero)]

open scoped Classical in
/-- **The image of `(a) ∪ (b)` in `H²(G_K, (Kˢ)ˣ)` on an explicit cocycle.** If `α² = a` and
`β² = b`, then `h2MuToUnits K ((a) ∪ (b))` is the class of the cocycle which is `-1` at `(g, k)`
when `g α ≠ α` and `k β ≠ β`, and `1` otherwise. -/
private theorem exists_h2MuToUnits_cup_kummerClass {a b : Kˣ} {α β : (SeparableClosure K)ˣ}
    (hα : α ^ 2 = Units.map (algebraMap K (SeparableClosure K)).toMonoidHom a)
    (hβ : β ^ 2 = Units.map (algebraMap K (SeparableClosure K)).toMonoidHom b) :
    ∃ W : Z2 (AbsoluteGaloisGroup K) (UnitsCoeff K),
      (h2MuToUnits K).hom ((trivialF2TopPairing (AbsoluteGaloisGroup K)).cup 1 1
        (kummerClass a) (kummerClass b)) =
        explicitH2AddEquivContinuousCohomology _ _ (W : H2 _ _) ∧
      ∀ g k, (W : AbsoluteGaloisGroup K × AbsoluteGaloisGroup K → UnitsCoeff K) (g, k) =
        Additive.ofMul (if g • α = α ∨ k • β = β then 1 else -1) := by
  -- transport the cup product to explicit cocycles
  rw [kummerClass_eq_kummerCocycleModTwoClass_of_sq_eq K a α hα,
    kummerClass_eq_kummerCocycleModTwoClass_of_sq_eq K b β hβ,
    trivialF2TopPairing_cup_one_one_explicitH1, h2MuToUnits_explicitH2]
  -- unfold the explicit classes to their representing cocycles
  rw [kummerCocycleModTwoClass_def, kummerCocycleModTwoClass_def, explicitCup11_mk,
    explicitCoeff2_mk, explicitCoeff2_mk]
  refine ⟨_, rfl, fun g k ↦ Additive.toMul.injective ?_⟩
  -- evaluate the two coefficient pullbacks at `(g, k)`; `rw [cocyclesMap2_apply]` cannot reach
  -- them, since the equivariance proof argument is not type-correct at reducible transparency
  refine (congrArg Additive.toMul (cocyclesMap2_apply _ _ _ _ _ _ _ _ _ g k)).trans ?_
  refine (congrArg (fun x ↦ Additive.toMul
    ((kummerShortExact K 2 (isUnit_of_invertible _)).inclDistribMulActionHom x))
      (cocyclesMap2_apply _ _ _ _ _ _ _ _ _ _ _)).trans ?_
  rw [DiscreteShortExact.inclDistribMulActionHom_apply, kummerShortExact_incl]
  -- `cocyclesMap2_apply` leaves the coefficient map as the coerced additive homomorphism of
  -- `trivialF2ToMu2 K`, evaluated at the identity of `G_K`; `change` exposes the equivariant map
  -- and the cocycle values that the value lemmas below are stated for.
  change (kummerCoeffIncl K 2 (trivialF2ToMu2 K (trivialF2Pairing _
    ((kummerCocycleModTwo K hα : _ → _) g) (g • (kummerCocycleModTwo K hβ : _ → _) k)))).toMul = _
  -- evaluate the coefficient values
  simp only [toMul_kummerCoeffIncl_trivialF2ToMu2, TopRep.distribMulAction_smul,
    trivialF2_ρ_apply_apply, trivialF2Pairing_apply, AddEquiv.apply_symm_apply,
    kummerCocycleModTwo_apply, toMul_ofMul]
  by_cases h₁ : g • α = α <;> by_cases h₂ : k • β = β <;>
    simp only [h₁, h₂, ↓reduceIte, mul_zero, mul_one, one_ne_zero, true_or, or_true, or_self]

/-! ### The coboundary -/

omit [Invertible (2 : K)] in
/-- The Galois conjugates of a square root of an element of `K` are itself and its negative: the
Kummer ratio `g α / α` is a square root of unity. -/
private theorem smul_eq_or_eq_neg {a : Kˣ} {α : (SeparableClosure K)ˣ}
    (hα : α ^ 2 = Units.map (algebraMap K (SeparableClosure K)).toMonoidHom a)
    (g : AbsoluteGaloisGroup K) : g • α = α ∨ g • α = -α := by
  have h := toMul_kummerCocycle hα g
  rcases toMul_eq_one_or_neg_one (kummerCocycle hα g) with h₁ | h₁
  · rw [h₁, OneMemClass.coe_one, eq_comm, mul_inv_eq_one] at h
    exact Or.inl h
  · rw [h₁, eq_comm, mul_inv_eq_iff_eq_mul, neg_one_mul] at h
    exact Or.inr h

omit [Invertible (2 : K)] in
/-- The Galois action on the units of `Kˢ` commutes with negation. -/
private theorem smul_neg_units (g : AbsoluteGaloisGroup K) (x : (SeparableClosure K)ˣ) :
    g • -x = -(g • x) := by
  rw [AlgEquiv.smul_units_def, AlgEquiv.smul_units_def, Units.map_neg]

/-- A unit of `Kˢ` is not its own negative, since `2` is invertible. -/
private theorem neg_ne_self_units (α : (SeparableClosure K)ˣ) : -α ≠ α := by
  have h2 := ((isUnit_of_invertible (2 : K)).map (algebraMap K (SeparableClosure K))).ne_zero
  rw [map_ofNat] at h2
  intro h
  have hv := congrArg Units.val h
  rw [Units.val_neg] at hv
  have h' : (2 : SeparableClosure K) * α = 0 := by
    linear_combination -hv
  exact α.ne_zero ((mul_eq_zero.1 h').resolve_left h2)

open scoped Classical in
/-- **The coboundary identity.** With `f(g) = 1` if `g α = α` and `f(g) = g β` otherwise, the
coboundary `g(f(k)) f(gk)⁻¹ f(g)` is the quotient of the quadratic cocycle of `b` by the cup
cocycle of `(a)` and `(b)`. -/
private theorem coboundary_eq {a b : Kˣ} {α β : (SeparableClosure K)ˣ}
    (hα : α ^ 2 = Units.map (algebraMap K (SeparableClosure K)).toMonoidHom a)
    (hβ : β ^ 2 = Units.map (algebraMap K (SeparableClosure K)).toMonoidHom b)
    (g k : AbsoluteGaloisGroup K) :
    (g • (if k • α = α then 1 else k • β)) / (if (g * k) • α = α then 1 else (g * k) • β) *
        (if g • α = α then 1 else g • β) =
      (if g • α = α ∨ k • α = α then 1
        else Units.map (algebraMap K (SeparableClosure K)).toMonoidHom b) /
        (if g • α = α ∨ k • β = β then 1 else -1) := by
  have hne := neg_ne_self_units α
  have hneβ := neg_ne_self_units β
  simp only [mul_smul]
  rcases smul_eq_or_eq_neg hα g with hg | hg <;> rcases smul_eq_or_eq_neg hα k with hk | hk <;>
    rcases smul_eq_or_eq_neg hβ k with hkβ | hkβ <;>
    simp only [hg, hk, hkβ, smul_neg_units, neg_neg, hne, hneβ, ↓reduceIte, or_true, or_self,
      or_false, smul_one, div_one, one_div, mul_one]
  all_goals first
    | exact div_self' _
    | exact inv_mul_cancel _
    | rw [← smul_mul', ← sq, hβ, smul_units_map_algebraMap]
    | rw [neg_mul, ← smul_mul', ← sq, hβ, smul_units_map_algebraMap, div_neg, div_one]
    | rw [← neg_inv, neg_mul, inv_mul_cancel, inv_neg_one]

open scoped Classical in
/-- **The inflated quadratic cocycle and the cup cocycle are cohomologous.** If `L ⊆ Kˢ` is a
quadratic Galois subextension whose automorphisms are detected by `α`, with `α² = a`, then the
inflation of the quadratic cocycle of `b` differs from the cup cocycle of `(a)` and `(b)` by a
continuous coboundary. -/
private theorem inflateZ2_quadratic_sub_mem_B2 {a b : Kˣ} {α β : (SeparableClosure K)ˣ}
    (hα : α ^ 2 = Units.map (algebraMap K (SeparableClosure K)).toMonoidHom a)
    (hβ : β ^ 2 = Units.map (algebraMap K (SeparableClosure K)).toMonoidHom b)
    (L : IntermediateField K (SeparableClosure K)) [FiniteDimensional K L] [IsGalois K L]
    (hcard : Nat.card (L ≃ₐ[K] L) = 2)
    (hr : ∀ g : AbsoluteGaloisGroup K, AlgEquiv.restrictNormalHom L g = 1 ↔ g • α = α)
    (W : Z2 (AbsoluteGaloisGroup K) (UnitsCoeff K))
    (hW : ∀ g k, (W : AbsoluteGaloisGroup K × AbsoluteGaloisGroup K → UnitsCoeff K) (g, k) =
      Additive.ofMul (if g • α = α ∨ k • β = β then 1 else -1)) :
    ((TwoCocycle.quadratic hcard b).inflateZ2 L :
        AbsoluteGaloisGroup K × AbsoluteGaloisGroup K → UnitsCoeff K) - W ∈
      B2 (AbsoluteGaloisGroup K) (UnitsCoeff K) := by
  refine mem_B2_iff'.2 ⟨fun g ↦ if g • α = α then 0 else Additive.ofMul (g • β), ?_, fun g k ↦ ?_⟩
  · -- the cochain factors through the orbit maps of `α` and `β`, which are continuous
    have hc : Continuous fun g : AbsoluteGaloisGroup K ↦
        (g • (Additive.ofMul α : UnitsCoeff K), g • (Additive.ofMul β : UnitsCoeff K)) :=
      (continuous_id.smul continuous_const).prodMk (continuous_id.smul continuous_const)
    exact (continuous_of_discreteTopology (f := fun p : UnitsCoeff K × UnitsCoeff K ↦
      if p.1.toMul = α then (0 : UnitsCoeff K) else p.2)).comp hc
  have hq : Units.map L.val.toRingHom.toMonoidHom ((TwoCocycle.quadratic hcard b).toFun
      (AlgEquiv.restrictNormalHom L g) (AlgEquiv.restrictNormalHom L k)) =
      if g • α = α ∨ k • α = α then 1
        else Units.map (algebraMap K (SeparableClosure K)).toMonoidHom b := by
    by_cases hg : g • α = α
    · rw [(hr g).2 hg, TwoCocycle.toFun_one_left, TwoCocycle.quadratic_toFun_one_right, map_one]
      simp only [hg, true_or, ↓reduceIte]
    by_cases hk : k • α = α
    · rw [(hr k).2 hk, TwoCocycle.quadratic_toFun_one_right, map_one]
      simp only [hk, or_true, ↓reduceIte]
    rw [TwoCocycle.quadratic_toFun_of_ne_one_of_ne_one hcard b (mt (hr g).1 hg) (mt (hr k).1 hk)]
    simp only [hg, hk, or_self, ↓reduceIte]
    ext
    simp
  simp only [Pi.sub_apply, hW, TwoCocycle.coe_inflateZ2, TwoCocycle.coe_toCocycles₂,
    TwoCocycle.inflate_toFun, hq]
  apply Additive.toMul.injective
  simp only [toMul_add, toMul_sub, Additive.toMul_smul, toMul_ofMul, apply_ite Additive.toMul,
    toMul_zero]
  exact coboundary_eq hα hβ g k

/-- **The cyclic class of `b` inflates to `(a) ∪ (b)`.** Let `L/K` be a quadratic Galois
subextension of `Kˢ/K`, and suppose that restriction to `L` is trivial exactly on the
automorphisms that fix a chosen square root `α` of `a`. Then the inflation of the quadratic
cocycle with value `b` is the image under `h2MuToUnits` of the cup product of the Kummer classes
of `a` and `b`.

Together with `TauCeti.quadraticNormQuotientEquiv_mk`, this says that under
`H²(Gal(L/K), Lˣ) ≃ Kˣ / N_{L/K}(Lˣ)`, the class of `b` inflates to `(a) ∪ (b)`. -/
theorem TwoCocycle.inflateClass_quadratic_eq_h2MuToUnits_cup {a b : Kˣ}
    {α : (SeparableClosure K)ˣ}
    (hα : α ^ 2 = Units.map (algebraMap K (SeparableClosure K)).toMonoidHom a)
    (L : IntermediateField K (SeparableClosure K)) [FiniteDimensional K L] [IsGalois K L]
    (hcard : Nat.card (L ≃ₐ[K] L) = 2)
    (hr : ∀ g : AbsoluteGaloisGroup K, AlgEquiv.restrictNormalHom L g = 1 ↔ g • α = α) :
    (TwoCocycle.quadratic hcard b).inflateClass L =
      (h2MuToUnits K).hom ((trivialF2TopPairing (AbsoluteGaloisGroup K)).cup 1 1
        (kummerClass a) (kummerClass b)) := by
  obtain ⟨β, hβ⟩ := exists_pow_eq_units_map (n := 2) (isUnit_of_invertible (2 : K)) b
  obtain ⟨W, hW, hWv⟩ := exists_h2MuToUnits_cup_kummerClass hα hβ
  rw [TwoCocycle.inflateClass_def, hW]
  exact congrArg _ (H2pi_eq_iff.2
    (inflateZ2_quadratic_sub_mem_B2 hα hβ L hcard hr W hWv))

/-! ### The symbol as a cup product -/

/-- **The quaternion symbol as a cup product.** The comparison `Br(K) ≃ H²_cont(G_K, (Kˢ)ˣ)` sends
the quaternion symbol `[(a, b)]` to the image under `h2MuToUnits K` of the cup product
`(a) ∪ (b) ∈ H²_cont(G_K, 𝔽₂)` of the Kummer classes of `a` and `b`. -/
theorem brauerCohomologyEquiv_quaternionClass (a b : Kˣ) :
    brauerCohomologyEquiv K (Additive.ofMul (BrauerGroup.quaternionClass a b)) =
      (h2MuToUnits K).hom ((trivialF2TopPairing (AbsoluteGaloisGroup K)).cup 1 1
        (kummerClass a) (kummerClass b)) := by
  by_cases ha : a ∈ Subgroup.square Kˣ
  · -- if `a` is a square, both sides vanish
    rw [(kummerClass_eq_zero_iff_square K).2 ha]
    obtain ⟨c, rfl⟩ := Subgroup.mem_square.1 ha
    rw [← sq, BrauerGroup.quaternionClass_sq_left, ofMul_one, map_zero]
    simp
  obtain ⟨α, hα⟩ := exists_pow_eq_units_map (n := 2) (isUnit_of_invertible (2 : K)) a
  have hα' : (α : SeparableClosure K) ^ 2 = algebraMap K _ a := by
    rw [← Units.val_pow_eq_pow_val, hα]
    rfl
  -- `L = K(α)` is a quadratic Galois subextension of `Kˢ`
  let L := K⟮(α : SeparableClosure K)⟯
  have h2 : Module.finrank K L = 2 :=
    IntermediateField.finrank_adjoin_simple_eq_two_of_not_isSquare hα'
    (mt isSquare_units_val_iff.1 (mt Subgroup.mem_square.2 ha))
  have : Algebra.IsQuadraticExtension K L := ⟨h2⟩
  have : FiniteDimensional K L := Module.finite_of_finrank_eq_succ h2
  have : IsGalois K L := Algebra.IsQuadraticExtension.isGalois K L
  have hcard : Nat.card (L ≃ₐ[K] L) = 2 := (IsGalois.card_aut_eq_finrank K L).trans h2
  have hgen : AdjoinSimple.gen K (α : SeparableClosure K) ^ 2 = algebraMap K L a :=
    Subtype.ext (by simpa using hα')
  have hgenK : AdjoinSimple.gen K (α : SeparableClosure K) ∉ Set.range (algebraMap K L) := by
    rintro ⟨c, hc⟩
    have hbot : K⟮(α : SeparableClosure K)⟯ = ⊥ :=
      adjoin_simple_eq_bot_iff.2 (mem_bot.2 ⟨c, congrArg L.val hc⟩)
    rw [show L = ⊥ from hbot, IntermediateField.finrank_bot] at h2
    exact absurd h2 (by norm_num)
  -- `[(a, b)]` is the class of the quadratic cocycle of `b` over `L`, whose inflation is
  -- cohomologous to the cup cocycle
  rw [← BrauerGroup.crossedProductClass_quadratic hcard hgen hgenK b,
    brauerCohomologyEquiv_crossedProductClass]
  exact TwoCocycle.inflateClass_quadratic_eq_h2MuToUnits_cup hα L hcard fun g ↦
    (AlgEquiv.restrictNormalHom_adjoin_simple_eq_one_iff (α := (α : SeparableClosure K)) g).trans
      (by rw [AlgEquiv.smul_units_def, Units.ext_iff]; rfl)

/-- **The symbol as a cup product, `ι [(a, b)] = (a) ∪ (b)`.** The identification
`Br(K)[2] ≃ H²_cont(G_K, 𝔽₂)` sends the quaternion symbol `[(a, b)]` to the cup product of the
Kummer classes of `a` and `b`. -/
theorem brauer2EquivH2_quaternionClass (a b : Kˣ) :
    brauer2EquivH2 K (Additive.ofMul ⟨BrauerGroup.quaternionClass a b,
      BrauerGroup.mem_twoTorsion.2 (BrauerGroup.quaternionClass_sq a b)⟩) =
      (trivialF2TopPairing (AbsoluteGaloisGroup K)).cup 1 1 (kummerClass a) (kummerClass b) :=
  h2MuToUnits_injective K (by
    rw [brauer2EquivH2_h2MuToUnits, brauerCohomologyEquiv_quaternionClass])

end TauCeti
