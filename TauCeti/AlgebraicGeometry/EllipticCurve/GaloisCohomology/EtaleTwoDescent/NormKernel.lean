/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.EtaleTwoDescent.Basic

/-!
# The image of the cohomological `2`-descent map is the kernel of the norm

Let `W : y² = f(x)` be an elliptic curve in characteristic-`≠ 2` normal form over a field `K` in
which `2` is invertible, and let `A = K[X] ⧸ (f)` be the étale algebra of the `2`-division cubic.
The cohomological `2`-descent map `H¹(G_K, E[2]) → Aˣ ⧸ (Aˣ)²`
(`TauCeti.TwoDescent.cohomologicalMap`) is injective and its image has square norm. This file
proves the converse: **every square class of `A` with square norm comes from `H¹(G_K, E[2])`**, so

```text
H¹(G_K, E[2]) ≃ ker (N : Aˣ ⧸ (Aˣ)² → Kˣ ⧸ (Kˣ)²).
```

This is the cohomological content of the identification of `E[2]` with the kernel of the norm
`Res_{A/K} μ₂ → μ₂` (Silverman X.1.4; Brumer and Kramer). The proof constructs the class
explicitly. Let `u ∈ Aˣ` have norm `c²`. Each nonzero point `S` of `E(Kˢ)[2]` is `(σ θ, 0)` for a
unique embedding `σ` of a factor field `K[X] ⧸ (p)` of `A` into `Kˢ`, and we choose a square root
`β S` of the conjugate `σ (u_p)` of the component of `u` at `p`, with `β O = 1`. The product of
the `β S` squares to the norm of `u`, so it is `± c` and is fixed by `G_K`. The ratios
`g β(g⁻¹ S) / β(S)` are then square roots of unity whose product over `S` is trivial, and there
is a unique point `z(g)` of `E(Kˢ)[2]` with `e₂(z(g), S) = g β(g⁻¹ S) / β(S)` for every `S`, by
the values of the Weil pairing on the Klein four-group `E(Kˢ)[2]`. The map `g ↦ z(g)` is a
continuous cocycle, and for `g` fixing `σ θ` its pairing with `(σ θ, 0)` is the Kummer cocycle
`g β / β` of `u_p`. So the factorwise images of its class are the Kummer classes of the components
of `u`, and its descent image is the square class of `u`.

Combined with the description of the cohomological Selmer conditions in
`TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Selmer.EtaleTwoDescent`, this identifies
the cohomological `2`-Selmer group with the explicit étale-algebra one.

## Main results

* `TauCeti.TwoDescent.range_cohomologicalMap_eq_ker_normM`: the image of the cohomological
  `2`-descent map is the kernel of the norm `Aˣ ⧸ (Aˣ)² → Kˣ ⧸ (Kˣ)²`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], X.1.4.
* A. Brumer and K. Kramer, *The rank of elliptic curves*, Duke Math. J. 44 (1977), for the
  `2`-descent through the cubic étale algebra and the kernel of the norm.
-/

public section

noncomputable section

open Polynomial TauCeti.ContCohomology

namespace TauCeti

variable {K : Type*} [Field K] {W : WeierstrassCurve K}

namespace TwoDescent

section Cocycle

variable (h2 : IsUnit ((2 : ℕ) : K)) {β : W.TorsionCoeff 2 → (SeparableClosure K)ˣ}
  (hsq : ∀ (g : AbsoluteGaloisGroup K) (S : W.TorsionCoeff 2), (g • β S) ^ 2 = β (g • S) ^ 2)

include hsq in
/-- The ratio `g β(g⁻¹ S) / β(S)` is a square root of unity. -/
private theorem smul_mul_inv_mem_rootsOfUnity_two (g : AbsoluteGaloisGroup K)
    (S : W.TorsionCoeff 2) :
    g • β (g⁻¹ • S) * (β S)⁻¹ ∈ rootsOfUnity 2 (SeparableClosure K) := by
  rw [mem_rootsOfUnity, mul_pow, hsq, smul_inv_smul, inv_pow, mul_inv_cancel]

/-- The ratio `g β(g⁻¹ S) / β(S)`, a square root of unity. -/
private def descentRatio (g : AbsoluteGaloisGroup K) (S : W.TorsionCoeff 2) : KummerCoeff K 2 :=
  Additive.ofMul ⟨_, smul_mul_inv_mem_rootsOfUnity_two hsq g S⟩

/-- The underlying unit of `descentRatio hsq g S` is `g β(g⁻¹ S) / β(S)`. -/
private theorem coe_toMul_descentRatio (g : AbsoluteGaloisGroup K) (S : W.TorsionCoeff 2) :
    ((descentRatio hsq g S).toMul : (SeparableClosure K)ˣ) = g • β (g⁻¹ • S) * (β S)⁻¹ :=
  (rfl)

/-- The ratios satisfy the cocycle identity for the action of `G_K` on functions of `S`. -/
private theorem descentRatio_mul (g h : AbsoluteGaloisGroup K) (S : W.TorsionCoeff 2) :
    descentRatio hsq (g * h) S = g • descentRatio hsq h (g⁻¹ • S) + descentRatio hsq g S := by
  refine Additive.toMul.injective (Subtype.ext ?_)
  simp only [toMul_add, Subgroup.coe_mul, Additive.toMul_smul, rootsOfUnity.coe_smul,
    coe_toMul_descentRatio, mul_inv_rev, mul_smul, smul_mul', smul_inv']
  group

/-- A square root of unity is its own inverse. -/
private theorem descentRatio_add_self (g : AbsoluteGaloisGroup K) (S : W.TorsionCoeff 2) :
    descentRatio hsq g S + descentRatio hsq g S = 0 := by
  refine Additive.toMul.injective (Subtype.ext ?_)
  rw [toMul_add, toMul_zero, ← sq, Subgroup.coe_pow, OneMemClass.coe_one]
  exact (mem_rootsOfUnity 2 _).1 (descentRatio hsq g S).toMul.2

include hsq in
/-- The ratio at the point at infinity is trivial. -/
private theorem descentRatio_zero (h0 : β 0 = 1) (g : AbsoluteGaloisGroup K) :
    descentRatio hsq g 0 = 0 := by
  refine Additive.toMul.injective (Subtype.ext ?_)
  simp [coe_toMul_descentRatio, h0]

/-- The ratios multiply to `g (∏ β) / ∏ β`, which is trivial when `∏ β` is fixed by `G_K`. -/
private theorem sum_descentRatio [Fintype (W.TorsionCoeff 2)]
    (hprod : ∀ g : AbsoluteGaloisGroup K, g • ∏ S, β S = ∏ S, β S) (g : AbsoluteGaloisGroup K) :
    ∑ S, descentRatio hsq g S = 0 := by
  refine Additive.toMul.injective (Subtype.ext ?_)
  simp only [toMul_sum, toMul_zero, SubmonoidClass.coe_finsetProd, coe_toMul_descentRatio,
    Finset.prod_mul_distrib, Finset.prod_inv_distrib, OneMemClass.coe_one]
  rw [← Finset.smul_prod',
    Fintype.prod_equiv (MulAction.toPerm g⁻¹) (fun S ↦ β (g⁻¹ • S)) β fun _ ↦ rfl, hprod,
    mul_inv_cancel]

open scoped Classical in
/-- The point of `E(Kˢ)[2]` pairing with every `S` to `descentRatio hsq g S`. -/
private def descentCocycle [Fintype (W.TorsionCoeff 2)] (g : AbsoluteGaloisGroup K) :
    W.TorsionCoeff 2 :=
  ∑ S, if descentRatio hsq g S = 0 then 0 else S

variable [W.IsElliptic]

include h2 in
open scoped Classical in
/-- **The defining property of `descentCocycle`**: `e₂(z(g), S) = g β(g⁻¹ S) / β(S)`. -/
private theorem torsionCoeffWeilPairing_descentCocycle [Fintype (W.TorsionCoeff 2)]
    (h0 : β 0 = 1) (hprod : ∀ g : AbsoluteGaloisGroup K, g • ∏ S, β S = ∏ S, β S)
    (g : AbsoluteGaloisGroup K) (S : W.TorsionCoeff 2) :
    W.torsionCoeffWeilPairing 2 h2 (descentCocycle hsq g) S = descentRatio hsq g S := by
  by_cases hS : S = 0
  · rw [hS, map_zero, descentRatio_zero hsq h0]
  -- the sum of the points `T` with nontrivial ratio pairs with `S ≠ O` to the product of the
  -- ratios at all `T ∉ {O, S}`, which is the ratio at `S` as all the ratios multiply to `1`
  rw [descentCocycle, W.torsionCoeffWeilPairing_sum_ite h2 _ hS, sum_descentRatio hsq hprod,
    descentRatio_zero hsq h0, sub_zero, zero_sub]
  exact neg_eq_of_add_eq_zero_right (descentRatio_add_self hsq g S)

include h2 in
/-- `descentCocycle` is a continuous `1`-cocycle. -/
private theorem descentCocycle_mem_Z1 [Fintype (W.TorsionCoeff 2)]
    (h0 : β 0 = 1) (hprod : ∀ g : AbsoluteGaloisGroup K, g • ∏ S, β S = ∏ S, β S) :
    descentCocycle hsq ∈ Z1 (AbsoluteGaloisGroup K) (W.TorsionCoeff 2) := by
  have he := torsionCoeffWeilPairing_descentCocycle h2 hsq h0 hprod
  -- the cocycle identity is that of the ratios, by nondegeneracy of the Weil pairing
  have hcoc : groupCohomology.IsCocycle₁ (descentCocycle hsq) := fun g h ↦ by
    rw [← sub_eq_zero]
    refine W.torsionCoeffWeilPairing_nondegenerate 2 h2 fun S ↦ ?_
    have hgS := W.torsionCoeffWeilPairing_smul 2 h2 g (descentCocycle hsq h) (g⁻¹ • S)
    rw [smul_inv_smul] at hgS
    rw [map_sub, map_add, AddMonoidHom.sub_apply, AddMonoidHom.add_apply, hgS, he, he, he,
      descentRatio_mul, sub_self]
  refine mem_Z1_iff.2 ⟨?_, hcoc⟩
  -- the cocycle vanishes on the open subgroup fixing every `β S` and every `S`
  let U : Set (AbsoluteGaloisGroup K) := ⋂ S, (MulAction.stabilizer (AbsoluteGaloisGroup K)
    (Additive.ofMul (β S) : UnitsCoeff K) : Set (AbsoluteGaloisGroup K)) ∩
      MulAction.stabilizer (AbsoluteGaloisGroup K) S
  have hU : IsOpen U :=
    isOpen_iInter_of_finite fun S ↦ (stabilizer_isOpen _ _).inter (stabilizer_isOpen _ _)
  have hzero {u : AbsoluteGaloisGroup K} (hu : u ∈ U) : descentCocycle hsq u = 0 := by
    refine W.torsionCoeffWeilPairing_nondegenerate 2 h2 fun S ↦ ?_
    obtain ⟨huβ, huS⟩ := Set.mem_iInter.1 hu S
    have huβ' : u • β S = β S := Additive.ofMul.injective huβ
    have huS' : u⁻¹ • S = S := inv_smul_eq_iff.2 huS.symm
    rw [he]
    refine Additive.toMul.injective (Subtype.ext ?_)
    rw [coe_toMul_descentRatio, huS', huβ', mul_inv_cancel, toMul_zero, OneMemClass.coe_one]
  refine IsLocallyConstant.continuous ((IsLocallyConstant.iff_exists_open _).2 fun g ↦ ?_)
  refine ⟨(g * ·) '' U, (Homeomorph.mulLeft g).isOpenMap _ hU,
    ⟨1, Set.mem_iInter.2 fun S ↦ ⟨one_smul _ _, one_smul _ _⟩, mul_one g⟩, ?_⟩
  rintro _ ⟨u, hu, rfl⟩
  rw [hcoc, hzero hu, smul_zero, zero_add]

end Cocycle

section NormKernel

variable (W) [W.IsElliptic] [W.toAffine.IsCharNeTwoNF]

local notation:max "𝕃" p:max => AdjoinRoot (p : K[X])
local notation:max "ι" p:max => algebraMap K (AdjoinRoot (p : K[X]))

omit [W.toAffine.IsCharNeTwoNF] in
/-- Restricting a class `[z]` to an extension `L` embedded by `σ` and applying a character `χ`
which reads, in `Kˢ`, as the Weil pairing with `T` gives the Kummer class of `a ∈ Lˣ`, provided
`e₂(z(g), T) = g b / b` on the automorphisms fixing `σ(L)`, for a square root `b` of `σ a`. -/
-- Stated over an arbitrary extension `L`: the same unfolding over a factor field is much slower.
private theorem explicitCoeff1_torsionRes_eq_kummerMap (h2 : IsUnit ((2 : ℕ) : K))
    {L : Type*} [Field L] [Algebra K L] (σ : L →ₐ[K] SeparableClosure K)
    (h2L : IsUnit ((2 : ℕ) : L))
    (χ : (W.baseChange L).TorsionCoeff 2 →+[AbsoluteGaloisGroup L] KummerCoeff L 2)
    (T : W.TorsionCoeff 2)
    (hχ : ∀ S, kummerCoeffMapSymm K 2 L σ (χ (W.torsionCoeffBaseChange
      (separableClosureAlgEquiv K L σ : SeparableClosure K →ₐ[K] SeparableClosure L) 2 S)) =
        W.torsionCoeffWeilPairing 2 h2 S T)
    (z : Z1 (AbsoluteGaloisGroup K) (W.TorsionCoeff 2)) {b : (SeparableClosure K)ˣ} {a : Lˣ}
    (ha : (b : SeparableClosure K) ^ 2 = σ a)
    (hz : ∀ g : AbsoluteGaloisGroup K, g ∈ σ.fieldRange.fixingSubgroup →
      ((W.torsionCoeffWeilPairing 2 h2 ((z : AbsoluteGaloisGroup K → W.TorsionCoeff 2) g)
        T).toMul : (SeparableClosure K)ˣ) = g • b * b⁻¹) :
    explicitCoeff1 (AbsoluteGaloisGroup L) ((W.baseChange L).TorsionCoeff 2) χ
        continuous_of_discreteTopology
        (W.torsionRes (separableClosureAlgEquiv K L σ :
          SeparableClosure K →ₐ[K] SeparableClosure L) 2 (z : H1 _ _)) =
      Multiplicative.toAdd (kummerMap L 2 h2L a) := by
  rw [kummerMap_eq_kummerCocycleClass h2L (units_map_separableClosureRingEquiv_symm_pow_eq σ ha),
    kummerCocycleClass_def, WeierstrassCurve.torsionRes_eq_explicitMap1, explicitMap1_mk,
    explicitCoeff1_mk]
  refine congrArg (H1pi (AbsoluteGaloisGroup L) (KummerCoeff L 2))
    (Subtype.ext (funext fun h ↦ ?_))
  refine ((cocyclesMap1_apply ..).trans (congrArg _ (cocyclesMap1_apply ..))).trans ?_
  apply Function.LeftInverse.injective (kummerCoeffMap_kummerCoeffMapSymm K 2 L σ)
  have hg : absoluteGaloisGroupMap
      (separableClosureAlgEquiv K L σ : SeparableClosure K →ₐ[K] SeparableClosure L)
      (ContinuousMonoidHom.id (AbsoluteGaloisGroup L) h) =
        (absoluteGaloisGroupEquivFixingSubgroup K L σ h : AbsoluteGaloisGroup K) := by
    simp [absoluteGaloisGroupMap_separableClosureAlgEquiv]
  refine (hχ _).trans ?_
  rw [hg]
  refine Additive.toMul.injective (Subtype.ext ?_)
  rw [hz _ (absoluteGaloisGroupEquivFixingSubgroup K L σ h).2, toMul_kummerCoeffMapSymm,
    toMul_kummerCocycle]
  ext
  simp [absoluteGaloisGroupEquivFixingSubgroup_apply, AlgEquiv.smul_units_def]

/-- **The factorwise images of the descent class.** If `β (σ θ, 0)` is a square root of `σ a`,
the image of the class of `descentCocycle` at the factor `p` is the Kummer class of `a`. -/
private theorem factorCohomologicalMap_descentCocycle [Fintype (W.TorsionCoeff 2)]
    (h2 : IsUnit ((2 : ℕ) : K)) {β : W.TorsionCoeff 2 → (SeparableClosure K)ˣ}
    (hsq : ∀ (g : AbsoluteGaloisGroup K) (S : W.TorsionCoeff 2), (g • β S) ^ 2 = β (g • S) ^ 2)
    (h0 : β 0 = 1) (hprod : ∀ g : AbsoluteGaloisGroup K, g • ∏ S, β S = ∏ S, β S)
    (p : W.toAffine.f.Factors) (σ : 𝕃 p →ₐ[K] SeparableClosure K) (a : (𝕃 p)ˣ)
    (ha : (β (embeddingTorsionCoeff W p σ) : SeparableClosure K) ^ 2 = σ a)
    (h2p : IsUnit ((2 : ℕ) : 𝕃 p)) :
    factorCohomologicalMap W p
        (separableClosureAlgEquiv K (𝕃 p) σ : SeparableClosure K →ₐ[K] SeparableClosure (𝕃 p)) h2
        ((⟨descentCocycle hsq, descentCocycle_mem_Z1 h2 hsq h0 hprod⟩ :
          Z1 (AbsoluteGaloisGroup K) (W.TorsionCoeff 2)) : H1 _ _) =
      Multiplicative.toAdd (kummerMap (𝕃 p) 2 h2p a) := by
  -- an automorphism fixing `σ(K[X] ⧸ (p))` fixes `(σ θ, 0)`, so the ratio there is `g b / b`
  have hz (g : AbsoluteGaloisGroup K) (hg : g ∈ σ.fieldRange.fixingSubgroup) :
      ((W.torsionCoeffWeilPairing 2 h2 (descentCocycle hsq g)
        (embeddingTorsionCoeff W p σ)).toMul : (SeparableClosure K)ˣ) =
        g • β (embeddingTorsionCoeff W p σ) * (β (embeddingTorsionCoeff W p σ))⁻¹ := by
    have hgσ : (g : SeparableClosure K →ₐ[K] SeparableClosure K).comp σ = σ :=
      AlgHom.ext fun x ↦ (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg (σ x) ⟨x, rfl⟩
    have hgT : g⁻¹ • embeddingTorsionCoeff W p σ = embeddingTorsionCoeff W p σ := by
      rw [inv_smul_eq_iff, smul_embeddingTorsionCoeff, hgσ]
    rw [torsionCoeffWeilPairing_descentCocycle h2 hsq h0 hprod, coe_toMul_descentRatio, hgT]
  exact (factorCohomologicalMap_apply ..).trans <|
    explicitCoeff1_torsionRes_eq_kummerMap W h2 σ h2p (factorTorsionCharacter W p h2)
    (embeddingTorsionCoeff W p σ) (kummerCoeffMapSymm_factorTorsionCharacter W p σ h2)
    ⟨descentCocycle hsq, descentCocycle_mem_Z1 h2 hsq h0 hprod⟩ ha hz

/-- The descent cocycle of square roots `β (σ θ, 0)` of the conjugates `σ (u_p)` of the
components of a unit `u` of the étale algebra is a class with descent image the square class of
`u`. -/
private theorem cohomologicalMap_descentCocycle [Fintype (W.TorsionCoeff 2)]
    (h2 : IsUnit ((2 : ℕ) : K)) {β : W.TorsionCoeff 2 → (SeparableClosure K)ˣ}
    (hsq : ∀ (g : AbsoluteGaloisGroup K) (S : W.TorsionCoeff 2), (g • β S) ^ 2 = β (g • S) ^ 2)
    (h0 : β 0 = 1) (hprod : ∀ g : AbsoluteGaloisGroup K, g • ∏ S, β S = ∏ S, β S)
    (u : W.toAffine.Aˣ)
    (hβ : ∀ (p : W.toAffine.f.Factors) (σ : 𝕃 p →ₐ[K] SeparableClosure K),
      (β (embeddingTorsionCoeff W p σ) : SeparableClosure K) ^ 2 =
        σ (AdjoinRoot.projFactor W.toAffine.f_ne_zero W.toAffine.squarefree_f p u)) :
    cohomologicalMap W h2 (.ofAdd ((⟨descentCocycle hsq, descentCocycle_mem_Z1 h2 hsq h0 hprod⟩ :
      Z1 (AbsoluteGaloisGroup K) (W.TorsionCoeff 2)) : H1 _ _)) = (u : W.toAffine.M) := by
  refine (explicitFactorEquiv W).injective (funext fun p ↦ ?_)
  have h2p : IsUnit ((2 : ℕ) : 𝕃 p) := by simpa only [map_natCast] using h2.map (ι p)
  have := AdjoinRoot.isSeparable_of_separable (WeierstrassCurve.Affine.separable_f W.toAffine) p
  let σ : 𝕃 p →ₐ[K] SeparableClosure K := IsSepClosed.lift
  rw [explicitFactorEquiv_apply, explicitFactorEquiv_apply]
  apply (kummerIso (𝕃 p) 2 h2p).injective
  refine (kummerIso_explicitFactor_cohomologicalMap W p (separableClosureAlgEquiv K (𝕃 p) σ :
    SeparableClosure K →ₐ[K] SeparableClosure (𝕃 p)) h2 h2p _).trans ?_
  -- term-mode composition: rewriting here unfolds the factor fields at great cost
  exact (congrArg Multiplicative.ofAdd
    (factorCohomologicalMap_descentCocycle W h2 hsq h0 hprod p σ _ (hβ p σ) h2p)).trans <|
      (ofAdd_toAdd _).trans <| (kummerIso_mk ..).symm.trans <|
        congrArg _ (explicitFactor_mk W p u).symm

/-- The norm of an element of the étale algebra is the product of the conjugates of its components,
over all the embeddings of the factor fields into `Kˢ`. -/
private theorem algebraMap_norm_eq_prod_projFactor [Fintype W.toAffine.f.Factors]
    (u : W.toAffine.A) :
    algebraMap K (SeparableClosure K) (Algebra.norm K u) =
      ∏ i : Σ p : W.toAffine.f.Factors, 𝕃 p →ₐ[K] SeparableClosure K,
        i.2 (AdjoinRoot.projFactor W.toAffine.f_ne_zero W.toAffine.squarefree_f i.1 u) := by
  rw [Fintype.prod_sigma,
    AdjoinRoot.norm_eq_prod_norm_projFactor W.toAffine.f_ne_zero W.toAffine.squarefree_f,
    map_prod]
  refine Finset.prod_congr rfl fun p _ ↦ ?_
  have := AdjoinRoot.isSeparable_of_separable (WeierstrassCurve.Affine.separable_f W.toAffine) p
  exact algebraMap_norm_eq_prod_algHom K (𝕃 p) _

/-- For a unit `u` of the étale algebra with square norm, square roots `β (σ θ, 0)` of the
conjugates `σ (u_p)` of its components can be chosen with `∏ β` fixed by `G_K`. -/
private theorem exists_descentRoots (h2 : IsUnit ((2 : ℕ) : K)) [Fintype (W.TorsionCoeff 2)]
    (u : W.toAffine.Aˣ) {c : Kˣ} (hc : c ^ 2 = Units.map (Algebra.norm K : W.toAffine.A →* K) u) :
    ∃ β : W.TorsionCoeff 2 → (SeparableClosure K)ˣ,
      (∀ (g : AbsoluteGaloisGroup K) (S : W.TorsionCoeff 2), (g • β S) ^ 2 = β (g • S) ^ 2) ∧
      β 0 = 1 ∧ (∀ g : AbsoluteGaloisGroup K, g • ∏ S, β S = ∏ S, β S) ∧
      ∀ (p : W.toAffine.f.Factors) (σ : 𝕃 p →ₐ[K] SeparableClosure K),
        (β (embeddingTorsionCoeff W p σ) : SeparableClosure K) ^ 2 =
          σ (AdjoinRoot.projFactor W.toAffine.f_ne_zero W.toAffine.squarefree_f p u) := by
  classical
  have : Finite W.toAffine.f.Factors := Polynomial.Factors.finite W.toAffine.f_ne_zero
  have := Fintype.ofFinite W.toAffine.f.Factors
  -- square roots of the conjugates of the components of `u`, indexed by the embeddings
  have hr (i : Σ p : W.toAffine.f.Factors, 𝕃 p →ₐ[K] SeparableClosure K) :
      ∃ r : (SeparableClosure K)ˣ, (r : SeparableClosure K) ^ 2 =
        i.2 (AdjoinRoot.projFactor W.toAffine.f_ne_zero W.toAffine.squarefree_f i.1 u) := by
    have : NeZero ((2 : ℕ) : SeparableClosure K) := ⟨h2.natCast_ne_zero_of_algebra⟩
    obtain ⟨r, hr⟩ := IsSepClosed.exists_pow_nat_eq
      (i.2 (AdjoinRoot.projFactor W.toAffine.f_ne_zero W.toAffine.squarefree_f i.1 u)) 2
    refine ⟨Units.mk0 r fun h ↦ ((u.isUnit.map (AdjoinRoot.projFactor W.toAffine.f_ne_zero
      W.toAffine.squarefree_f i.1)).map i.2).ne_zero ?_, hr⟩
    rw [← hr, h, zero_pow two_ne_zero]
  choose r hr using hr
  -- reindexed by the nonzero points of order two
  let e := Equiv.ofBijective _ (bijective_embeddingTorsionCoeff W h2)
  let β (S : W.TorsionCoeff 2) : (SeparableClosure K)ˣ :=
    if h : S = 0 then 1 else r (e.symm ⟨S, h⟩)
  have h0 : β 0 = 1 := dite_eq_left rfl
  have hβ (i : Σ p : W.toAffine.f.Factors, 𝕃 p →ₐ[K] SeparableClosure K) :
      β (embeddingTorsionCoeff W i.1 i.2) = r i := by
    simp only [β, dite_eq_right (embeddingTorsionCoeff_ne_zero W i.1 i.2)]
    exact congrArg r (e.symm_apply_apply i)
  refine ⟨β, fun g S ↦ ?_, h0, fun g ↦ ?_, fun p σ ↦ by rw [hβ ⟨p, σ⟩, hr]⟩
  · by_cases hS : S = 0
    · rw [hS, smul_zero, h0, smul_one]
    obtain ⟨⟨p, τ⟩, rfl⟩ : ∃ i : Σ p : W.toAffine.f.Factors, 𝕃 p →ₐ[K] SeparableClosure K,
        embeddingTorsionCoeff W i.1 i.2 = S :=
      ⟨e.symm ⟨S, hS⟩, congrArg Subtype.val (e.apply_symm_apply ⟨S, hS⟩)⟩
    rw [smul_embeddingTorsionCoeff, hβ ⟨p, τ⟩, hβ ⟨p, (g : _ →ₐ[K] _).comp τ⟩]
    ext
    simp [AlgEquiv.smul_units_def, ← map_pow, hr]
  -- the product of the square roots squares to the norm `c ^ 2` of `u`, so it is `± c`
  have hP : ((∏ S, β S : (SeparableClosure K)ˣ) : SeparableClosure K) ^ 2 =
      algebraMap K (SeparableClosure K) c ^ 2 := by
    rw [Units.coe_prod, ← Finset.prod_pow, Fintype.prod_eq_mul_prod_compl 0, h0, Units.val_one,
      one_pow, one_mul, Finset.prod_subtype ({0}ᶜ : Finset _) (p := fun S ↦ S ≠ 0) (by simp),
      ← Fintype.prod_equiv e
        (fun i ↦ (β (embeddingTorsionCoeff W i.1 i.2) : SeparableClosure K) ^ 2) _ fun _ ↦ rfl]
    simp only [hβ, hr]
    rw [← map_pow, ← Units.val_pow_eq_pow_val, hc, Units.coe_map]
    exact (algebraMap_norm_eq_prod_projFactor W _).symm
  ext
  rw [AlgEquiv.smul_units_def, Units.coe_map]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 hP with h | h <;> simp [h]

/-- **The image of the cohomological `2`-descent map is the kernel of the norm** (Silverman
X.1.4): a square class of the étale algebra `K[X] ⧸ (f)` of the `2`-division cubic lies in the
image of `H¹(G_K, E[2])` exactly when its norm is a square in `K`. Together with
`TauCeti.TwoDescent.cohomologicalMap_injective` this identifies `H¹(G_K, E[2])` with the kernel of
the norm. -/
theorem range_cohomologicalMap_eq_ker_normM (h2 : IsUnit ((2 : ℕ) : K)) :
    (cohomologicalMap W h2).range = W.toAffine.normM.ker := by
  refine le_antisymm (range_cohomologicalMap_le_ker_normM W h2) fun m hm ↦ ?_
  have := Fintype.ofFinite (W.TorsionCoeff 2)
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective m
  rw [MonoidHom.mem_ker, WeierstrassCurve.Affine.normM_mk, QuotientGroup.eq_one_iff] at hm
  obtain ⟨c, hc⟩ := hm
  obtain ⟨β, hsq, h0, hprod, hβ⟩ := exists_descentRoots W h2 u hc
  exact ⟨_, cohomologicalMap_descentCocycle W h2 hsq h0 hprod u hβ⟩

end NormKernel

end TwoDescent

end TauCeti
