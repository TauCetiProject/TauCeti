/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.Relative.Basic
public import TauCeti.Geometry.Manifold.SmoothSingular.DeRham
import TauCeti.AlgebraicTopology.SimplicialSet.Homology.Coproduct

/-!
# Relative integration over smooth chains

Let `W` be an open subset of a manifold `M`. Integration of forms over smooth singular simplices
(`TauCeti.deRhamIntegration`) commutes with restriction to `W`, so it induces a map of mapping
cocones from the relative de Rham complex of `(M, W)` (`TauCeti.relativeDeRhamComplex`) to the
cocone of the restriction of real smooth singular cochains from `M` to `W`
(`TauCeti.relativeSmoothCochainComplex`). This map is *relative integration*
`TauCeti.relativeDeRhamIntegration`. In relative coordinates it integrates both components: it
sends `(α, β)` to `(∫ α, ∫ β)`, where `α` is a form on `M` and `β` a form on `W`
(`TauCeti.relativeCoordinates_relativeDeRhamIntegration_f`).

A relative smooth cycle of degree `k + 1` is a smooth `(k + 1)`-chain `c` of `M` whose boundary
lies in `W`: `∂c = c'` for a smooth `k`-chain `c'` of `W`, read in `M`. A relative smooth cochain
with coordinates `(a, b)` takes the value `a(c) - b(c')` on it
(`TauCeti.relativeSmoothCochainComplex.eval`). This pairing vanishes on coboundaries
(`TauCeti.relativeSmoothCochainComplex.eval_d`): in coordinates `d (a, b) = (da, a|_W - db)`, and
`da(c) = a(∂c) = a(c')` cancels `a|_W (c')`, while `db(c') = b(∂c') = 0`. On the relative
integral of `(α, β)` it is

`∫_c α - ∫_{c'} β`

(`TauCeti.relativeSmoothCochainComplex.eval_relativeDeRhamIntegration_f_coord_symm`). Hence every
relative smooth cycle integrates relative de Rham classes: there is a linear map
`TauCeti.relativeDeRhamCohomology.integral` from `H^(k+1)(M, W)` to `ℝ` taking the class of a
relative cocycle `(α, β)` to `∫_c α - ∫_{c'} β`
(`TauCeti.relativeDeRhamCohomology.integral_mk`).

For a closed form `α` vanishing on `W` this is `∫_c α`, the integral of `α` over a chain whose
boundary avoids the region where `α` is nonzero. This is how the integral of a compactly
supported top form is compared with the fundamental class of a manifold along its support: a
positively oriented simplex around the support is a relative cycle of the pair formed by the
manifold and the complement of the support.

The cochain-level construction needs no finite dimensionality, separation or countability of
`M`.

## Main definitions

* `TauCeti.smoothCochainRestriction I W`: restriction of real smooth singular cochains from `M`
  to `W`, extended to `ℤ`.
* `TauCeti.relativeSmoothCochainComplex I W`: its mapping cocone.
* `TauCeti.relativeDeRhamIntegration I W`: relative integration, a cochain map from the relative de
  Rham complex to the relative smooth cochain complex.
* `TauCeti.relativeSmoothCochainComplex.eval`: the pairing of relative smooth cochains with pairs
  of smooth chains.
* `TauCeti.relativeDeRhamCohomology.integral`: the integral of relative de Rham classes over a
  relative smooth cycle.

## References

* R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*, Graduate Texts in Mathematics
  82, Springer, 1982, Chapter I, §6 (the relative de Rham complex of a map).
* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 18 (integration over smooth
  chains and the de Rham homomorphism).
-/

public section

noncomputable section

open CategoryTheory HomologicalComplex TopologicalSpace CochainComplex.mappingCocone
open scoped ContDiff

namespace TauCeti

variable {E H : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) {M : Type} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 2 M] (W : Opens M)

/-- The complex of real smooth singular chains of `X`. -/
local notation "𝒮[" X "]" =>
  SSet.chainComplex (smoothSingularSubcomplex I X : SSet) (ModuleCat.of ℝ ℝ)

/-- The complex of real smooth singular cochains of `X`. -/
local notation "𝒞[" X "]" => ChainComplex.linearYonedaObj 𝒮[X] ℝ (ModuleCat.of ℝ ℝ)

/-- The restriction of real smooth singular cochains from `M` to the open subset `W`, as a map of
cochain complexes extended by zero to `ℤ`: precomposition with the chain map induced by the
inclusion of `W`. -/
def smoothCochainRestriction :
    𝒞[M].extend ComplexShape.embeddingUpNat ⟶ 𝒞[W].extend ComplexShape.embeddingUpNat :=
  extendMap (SSet.cochainComplexMap
    (smoothSingularSubcomplexMap (Subtype.val : W → M) contMDiff_subtypeVal)) _

/-- The relative smooth singular cochain complex of the open pair `(M, W)`, with real
coefficients: the mapping cocone of the restriction of smooth cochains from `M` to `W`. -/
abbrev relativeSmoothCochainComplex : CochainComplex (ModuleCat ℝ) ℤ :=
  CochainComplex.mappingCocone (smoothCochainRestriction I W)

/-- Integration over smooth simplices commutes with restriction to `W`. -/
@[reassoc]
theorem deRhamRestriction_comp_extendMap_deRhamIntegration :
    deRhamRestriction I W ≫ extendMap (deRhamIntegration I W) ComplexShape.embeddingUpNat =
      extendMap (deRhamIntegration I M) ComplexShape.embeddingUpNat ≫
        smoothCochainRestriction I W := by
  rw [deRhamRestriction_def, smoothCochainRestriction, ← extendMap_comp, ← extendMap_comp,
    deRhamIntegration_naturality]

/-- **Relative integration.** The cochain map from the relative de Rham complex of `(M, W)` to the
relative smooth cochain complex induced by integration over smooth simplices. In relative
coordinates it sends `(α, β)` to `(∫ α, ∫ β)`. -/
def relativeDeRhamIntegration : relativeDeRhamComplex I W ⟶ relativeSmoothCochainComplex I W :=
  (CochainComplex.mappingCone.map _ _ _ _
    (deRhamRestriction_comp_extendMap_deRhamIntegration I W))⟦(-1 : ℤ)⟧'

/-- In relative coordinates, relative integration integrates both components. -/
@[simp]
theorem relativeCoordinates_relativeDeRhamIntegration_f (p q : ℤ) (hpq : p + -1 = q)
    (x : (relativeDeRhamComplex I W).X p) :
    relativeCoordinates (smoothCochainRestriction I W) p q hpq
        ((relativeDeRhamIntegration I W).f p x) =
      ((extendMap (deRhamIntegration I M) ComplexShape.embeddingUpNat).f p
          (relativeCoordinates (deRhamRestriction I W) p q hpq x).1,
        (extendMap (deRhamIntegration I W) ComplexShape.embeddingUpNat).f q
          (relativeCoordinates (deRhamRestriction I W) p q hpq x).2) :=
  -- `relativeDeRhamIntegration` is typed between the mapping cocones, while
  -- `relativeCoordinates_map` is stated for the shifted cone map; they agree by unfolding.
  relativeCoordinates_map _ _ _ _ _ p q hpq x

namespace relativeSmoothCochainComplex

/-- **The pairing of relative smooth cochains with pairs of chains.** For a smooth
`(k + 1)`-chain `c` of `M` and a smooth `k`-chain `c'` of `W`, a relative smooth cochain of degree
`k + 1` with relative coordinates `(a, b)` takes the value `a(c) - b(c')`. On relative cycles,
`∂c = c'` read in `M`, it vanishes on coboundaries (`eval_d`). -/
def eval (k : ℕ)
    (c : 𝒮[M].X (k + 1))
    (c' : 𝒮[W].X k) :
    (relativeSmoothCochainComplex I W).X (k + 1 : ℕ) →ₗ[ℝ] ℝ :=
  LinearMap.applyₗ c ∘ₗ ModuleCat.homLinearEquiv.toLinearMap ∘ₗ
      (extendXIso 𝒞[M] ComplexShape.embeddingUpNat rfl).hom.hom ∘ₗ LinearMap.fst ℝ _ _ ∘ₗ
        (relativeCoordinates (smoothCochainRestriction I W) (k + 1 : ℕ) k
          (by push_cast; lia)).toLinearMap -
    LinearMap.applyₗ c' ∘ₗ ModuleCat.homLinearEquiv.toLinearMap ∘ₗ
      (extendXIso 𝒞[W] ComplexShape.embeddingUpNat rfl).hom.hom ∘ₗ LinearMap.snd ℝ _ _ ∘ₗ
        (relativeCoordinates (smoothCochainRestriction I W) (k + 1 : ℕ) k
          (by push_cast; lia)).toLinearMap

omit [IsManifold I 2 M] in
/-- The pairing of a relative cochain with coordinates `(a, b)` is `a(c) - b(c')`. -/
theorem eval_apply (k : ℕ)
    (c : 𝒮[M].X (k + 1))
    (c' : 𝒮[W].X k)
    (x : (relativeSmoothCochainComplex I W).X (k + 1 : ℕ)) :
    eval I W k c c' x =
      ((extendXIso 𝒞[M] ComplexShape.embeddingUpNat rfl).hom
          (relativeCoordinates (smoothCochainRestriction I W) (k + 1 : ℕ) k (by push_cast; lia)
            x).1).hom c -
        ((extendXIso 𝒞[W] ComplexShape.embeddingUpNat rfl).hom
          (relativeCoordinates (smoothCochainRestriction I W) (k + 1 : ℕ) k (by push_cast; lia)
            x).2).hom c' := by
  simp only [eval, LinearMap.sub_apply, LinearMap.comp_apply]
  rfl

omit [IsManifold I 2 M] in
/-- The boundary of the `W`-part of a relative smooth cycle vanishes: the chain map induced by
the inclusion of `W` is injective and carries `∂c'` to `∂∂c = 0`. -/
private theorem d_eq_zero_of_d_eq (j : ℕ)
    {c : 𝒮[M].X (j + 1 + 1)}
    {c' : 𝒮[W].X (j + 1)}
    (hc : 𝒮[M].d (j + 1 + 1) (j + 1) c =
      (SSet.chainComplexMap (smoothSingularSubcomplexMap (Subtype.val : W → M)
        contMDiff_subtypeVal) (ModuleCat.of ℝ ℝ)).f (j + 1) c') :
    𝒮[W].d (j + 1) j c' = 0 := by
  have := mono_smoothSingularSubcomplexMap (I := I) (J := I) contMDiff_subtypeVal
    (Subtype.val_injective (p := (· ∈ W)))
  apply (ModuleCat.mono_iff_injective ((SSet.chainComplexMap (smoothSingularSubcomplexMap
    (Subtype.val : W → M) contMDiff_subtypeVal) (ModuleCat.of ℝ ℝ)).f j)).mp inferInstance
  have h := ConcreteCategory.congr_hom ((SSet.chainComplexMap (smoothSingularSubcomplexMap
    (Subtype.val : W → M) contMDiff_subtypeVal) (ModuleCat.of ℝ ℝ)).comm (j + 1) j) c'
  simp only [ModuleCat.comp_apply] at h
  rw [map_zero, ← h, ← hc, ← ModuleCat.comp_apply, HomologicalComplex.d_comp_d]
  rfl

omit [IsManifold I 2 M] in
/-- On the `W`-part `c'` of a relative smooth cycle, the coboundary `db` of a cochain of `W` of
degree `k - 1` vanishes: `(db)(c') = b(∂c')` and `∂c' = 0`. In degree `0` the cochain `b` lies in
a zero module. -/
private theorem hom_extendXIso_hom_extend_d_apply_eq_zero (k : ℕ) {c : 𝒮[M].X (k + 1)}
    {c' : 𝒮[W].X k}
    (hc : 𝒮[M].d (k + 1) k c =
      (SSet.chainComplexMap (smoothSingularSubcomplexMap (Subtype.val : W → M)
        contMDiff_subtypeVal) (ModuleCat.of ℝ ℝ)).f k c')
    (b : (𝒞[W].extend ComplexShape.embeddingUpNat).X ((k : ℤ) + -1)) :
    ((extendXIso 𝒞[W] ComplexShape.embeddingUpNat rfl).hom
      ((𝒞[W].extend ComplexShape.embeddingUpNat).d ((k : ℤ) + -1) k b)).hom c' = 0 := by
  cases k with
  | zero =>
    have : Subsingleton ((𝒞[W].extend ComplexShape.embeddingUpNat).X ((0 : ℕ) + -1)) :=
      ModuleCat.subsingleton_of_isZero <| isZero_extend_X _ _ _ fun n hn ↦ by
        have : (0 : ℤ) ≤ n := Int.natCast_nonneg n
        simp only [ComplexShape.embeddingUpNat_f] at hn
        lia
    rw [Subsingleton.elim b 0, map_zero, map_zero]
    rfl
  | succ j =>
    have hmor : (𝒞[W].extend ComplexShape.embeddingUpNat).d
        (((j + 1 : ℕ) : ℤ) + -1) (j + 1 : ℕ) ≫
          (extendXIso 𝒞[W] ComplexShape.embeddingUpNat rfl).hom =
        (extendXIso 𝒞[W] ComplexShape.embeddingUpNat (i := j)
          (by simp only [ComplexShape.embeddingUpNat_f]; lia)).hom ≫
          𝒞[W].d j (j + 1) := by
      rw [extend_d_eq _ ComplexShape.embeddingUpNat (i' := ((j + 1 : ℕ) : ℤ) + -1)
        (j' := ((j + 1 : ℕ) : ℤ)) (i := j) (j := j + 1)
        (by simp only [ComplexShape.embeddingUpNat_f]; lia) rfl]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    have h := ConcreteCategory.congr_hom hmor b
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h
    rw [h]
    have h0 : (𝒮[W].d (j + 1) j).hom c' = 0 := d_eq_zero_of_d_eq I W j hc
    -- `(d g)(c') = g(∂c')` holds by definition, as in `hA`.
    exact (congrArg (ModuleCat.Hom.hom ((extendXIso 𝒞[W] ComplexShape.embeddingUpNat
      (i := j) (by simp only [ComplexShape.embeddingUpNat_f]; lia)).hom b)) h0).trans
        (map_zero _)

omit [IsManifold I 2 M] in
/-- **Relative cycles annihilate coboundaries.** If `∂c = c'` in `M`, the pairing with `(c, c')`
vanishes on the differential of every relative smooth cochain. -/
theorem eval_d (k : ℕ)
    {c : 𝒮[M].X (k + 1)}
    {c' : 𝒮[W].X k}
    (hc : 𝒮[M].d (k + 1) k c =
      (SSet.chainComplexMap (smoothSingularSubcomplexMap (Subtype.val : W → M)
        contMDiff_subtypeVal) (ModuleCat.of ℝ ℝ)).f k c')
    (y : (relativeSmoothCochainComplex I W).X k) :
    eval I W k c c' ((relativeSmoothCochainComplex I W).d k (k + 1 : ℕ) y) = 0 := by
  -- The target degree `((k + 1 : ℕ) : ℤ)` of `eval` is definitionally the `(k : ℤ) + 1` of
  -- `relativeCoordinates_d`, since `Int` addition computes on casts of natural numbers.
  have hd : relativeCoordinates (smoothCochainRestriction I W) (k + 1 : ℕ) k (by push_cast; lia)
      ((relativeSmoothCochainComplex I W).d k (k + 1 : ℕ) y) = _ :=
    relativeCoordinates_d _ k (k + -1) rfl y
  set a := (relativeCoordinates (smoothCochainRestriction I W) k (k + -1) rfl y).1
  set b := (relativeCoordinates (smoothCochainRestriction I W) k (k + -1) rfl y).2
  -- The three terms of `eval` on `d (a, b) = (da, a|_W - db)`, read in the unextended complexes.
  -- In each, the cochain `d g` (resp. `g|_W`) is by definition `g ∘ ∂` (resp. `g ∘ ι`), and
  -- evaluating a composite is applying its factors, so the last step of each is `rfl`.
  have hA : ((extendXIso 𝒞[M] ComplexShape.embeddingUpNat (i := k + 1) (by simp)).hom
      ((𝒞[M].extend ComplexShape.embeddingUpNat).d k ((k : ℤ) + 1) a)).hom c =
        ((extendXIso 𝒞[M] ComplexShape.embeddingUpNat rfl).hom a).hom
          ((𝒮[M].d (k + 1) k).hom c) := by
    have hmor : (𝒞[M].extend ComplexShape.embeddingUpNat).d k
        ((k : ℤ) + 1) ≫ (extendXIso 𝒞[M] ComplexShape.embeddingUpNat (i := k + 1) (by simp)).hom =
          (extendXIso 𝒞[M] ComplexShape.embeddingUpNat rfl).hom ≫ 𝒞[M].d k (k + 1) := by
      rw [extend_d_eq _ ComplexShape.embeddingUpNat (i' := (k : ℤ)) (j' := (k : ℤ) + 1) (i := k)
        (j := k + 1) rfl (by simp)]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    have h := ConcreteCategory.congr_hom hmor a
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h
    rw [h]
    rfl
  have hB : ((extendXIso 𝒞[W] ComplexShape.embeddingUpNat rfl).hom
      ((smoothCochainRestriction I W).f k a)).hom c' =
        ((extendXIso 𝒞[M] ComplexShape.embeddingUpNat rfl).hom a).hom
          (((SSet.chainComplexMap (smoothSingularSubcomplexMap (Subtype.val : W → M)
            contMDiff_subtypeVal) (ModuleCat.of ℝ ℝ)).f k).hom c') := by
    have hmor : (smoothCochainRestriction I W).f k ≫
        (extendXIso 𝒞[W] ComplexShape.embeddingUpNat rfl).hom =
          (extendXIso 𝒞[M] ComplexShape.embeddingUpNat rfl).hom ≫
            (SSet.cochainComplexMap (smoothSingularSubcomplexMap (Subtype.val : W → M)
              contMDiff_subtypeVal)).f k := by
      rw [smoothCochainRestriction,
        extendMap_f _ ComplexShape.embeddingUpNat (i' := (k : ℤ)) (i := k) rfl]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    have h := ConcreteCategory.congr_hom hmor a
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h
    rw [h]
    rfl
  -- `hc` is stated with the coercion of morphisms to functions, which for `ModuleCat` is
  -- definitionally `ModuleCat.Hom.hom`.
  have hc' : (𝒮[M].d (k + 1) k).hom c = ((SSet.chainComplexMap (smoothSingularSubcomplexMap
      (Subtype.val : W → M) contMDiff_subtypeVal) (ModuleCat.of ℝ ℝ)).f k).hom c' := hc
  -- Subtraction of cochains is subtraction of the underlying linear maps.
  have hsub (u v : 𝒞[W].X k) : (u - v).hom c' = u.hom c' - v.hom c' := rfl
  rw [eval_apply, hd, map_sub, hsub, hA, hB, hc', sub_sub_cancel]
  exact hom_extendXIso_hom_extend_d_apply_eq_zero I W k hc b

/-- **The evaluation formula.** The relative integral of `(α, β)` pairs with `(c, c')` to
`∫_c α - ∫_{c'} β`. -/
theorem eval_relativeDeRhamIntegration_f_coord_symm (k : ℕ)
    (c : 𝒮[M].X (k + 1))
    (c' : 𝒮[W].X k)
    (α : SmoothForm I M ℝ (k + 1)) (β : SmoothForm I W ℝ k) :
    eval I W k c c' ((relativeDeRhamIntegration I W).f (k + 1 : ℕ)
        ((relativeDeRhamComplex.coord I W k).symm (α, β))) =
      (integrationCochain α.val).hom c - (integrationCochain β.val).hom c' := by
  -- Relative integration acts on the extended complexes; read it back on the unextended ones.
  have hαmor :
      (extendXIso (deRhamComplex I M) ComplexShape.embeddingUpNat rfl).inv ≫
        (extendMap (deRhamIntegration I M) ComplexShape.embeddingUpNat).f (k + 1 : ℕ) ≫
          (extendXIso 𝒞[M] ComplexShape.embeddingUpNat rfl).hom =
            (deRhamIntegration I M).f (k + 1) := by
    rw [extendMap_f _ ComplexShape.embeddingUpNat (i' := ((k + 1 : ℕ) : ℤ)) (i := k + 1) rfl]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.inv_hom_id_assoc]
  have hα := ConcreteCategory.congr_hom hαmor ((deRhamComplexXIso I (k + 1)).inv α)
  have hβmor :
      (extendXIso (deRhamComplex I W) ComplexShape.embeddingUpNat rfl).inv ≫
        (extendMap (deRhamIntegration I W) ComplexShape.embeddingUpNat).f (k : ℤ) ≫
          (extendXIso 𝒞[W] ComplexShape.embeddingUpNat rfl).hom = (deRhamIntegration I W).f k := by
    rw [extendMap_f _ ComplexShape.embeddingUpNat (i' := (k : ℤ)) (i := k) rfl]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.inv_hom_id_assoc]
  have hβ := ConcreteCategory.congr_hom hβmor ((deRhamComplexXIso I k).inv β)
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, deRhamIntegration_f_inv_apply]
    at hα hβ
  rw [eval_apply, relativeCoordinates_relativeDeRhamIntegration_f,
    relativeDeRhamComplex.coord_symm_apply, map_add, relativeDeRhamComplex.relativeCoordinates_inl,
    relativeDeRhamComplex.relativeCoordinates_inr, Prod.mk_add_mk, add_zero, zero_add]
  dsimp only
  rw [deRhamComplexExtendXEquiv_symm_apply, deRhamComplexExtendXEquiv_symm_apply, hα, hβ]

end relativeSmoothCochainComplex

namespace relativeDeRhamCohomology

open relativeDeRhamComplex

/-- The integral over `(c, c')` of a relative de Rham cocycle of degree `k + 1`, through relative
integration. -/
private def cycleIntegral (k : ℕ) (c : 𝒮[M].X (k + 1)) (c' : 𝒮[W].X k) :
    (relativeDeRhamComplex I W).cycles (k + 1 : ℕ) →ₗ[ℝ] ℝ :=
  relativeSmoothCochainComplex.eval I W k c c' ∘ₗ
    ((relativeDeRhamIntegration I W).f (k + 1 : ℕ)).hom ∘ₗ
      ((relativeDeRhamComplex I W).iCycles (k + 1 : ℕ)).hom

/-- `cycleIntegral` only depends on the class of a relative cocycle, because relative integration
is a cochain map and relative cycles annihilate coboundaries. -/
private theorem cycleIntegral_eq_of_homologyπ_eq (k : ℕ) {c : 𝒮[M].X (k + 1)} {c' : 𝒮[W].X k}
    (hc : 𝒮[M].d (k + 1) k c =
      (SSet.chainComplexMap (smoothSingularSubcomplexMap (Subtype.val : W → M)
        contMDiff_subtypeVal) (ModuleCat.of ℝ ℝ)).f k c')
    {z w : (relativeDeRhamComplex I W).cycles (k + 1 : ℕ)}
    (h : (relativeDeRhamComplex I W).homologyπ (k + 1 : ℕ) z =
      (relativeDeRhamComplex I W).homologyπ (k + 1 : ℕ) w) :
    cycleIntegral I W k c c' z = cycleIntegral I W k c c' w := by
  obtain ⟨y, hy⟩ := ((relativeDeRhamComplex I W).moduleCat_homologyπ_eq_iff
    (m := (k : ℤ)) (by simp) z w).mp h
  have h' := ConcreteCategory.congr_hom ((relativeDeRhamIntegration I W).comm k (k + 1 : ℕ)) y
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hy, map_sub] at h'
  have h0 := relativeSmoothCochainComplex.eval_d I W k hc ((relativeDeRhamIntegration I W).f k y)
  rw [h', map_sub, sub_eq_zero] at h0
  exact h0

/-- A relative cocycle representing a relative de Rham class of degree `k + 1`. -/
private def classRep (k : ℕ) (x : relativeDeRhamCohomology I W (k + 1 : ℕ)) :
    (relativeDeRhamComplex I W).cycles (k + 1 : ℕ) :=
  ((relativeDeRhamComplex I W).moduleCat_homologyπ_surjective _ x).choose

private theorem homologyπ_classRep (k : ℕ) (x : relativeDeRhamCohomology I W (k + 1 : ℕ)) :
    (relativeDeRhamComplex I W).homologyπ (k + 1 : ℕ) (classRep I W k x) = x :=
  ((relativeDeRhamComplex I W).moduleCat_homologyπ_surjective _ x).choose_spec

/-- **The integral of relative de Rham classes over a relative smooth cycle.** For a smooth
`(k + 1)`-chain `c` of `M` whose boundary is a smooth `k`-chain `c'` of `W`, the linear map on
`H^(k+1)(M, W)` taking the class of a relative cocycle `(α, β)` to `∫_c α - ∫_{c'} β`
(`integral_mk`). -/
def integral (k : ℕ) {c : 𝒮[M].X (k + 1)} {c' : 𝒮[W].X k}
    (hc : 𝒮[M].d (k + 1) k c =
      (SSet.chainComplexMap (smoothSingularSubcomplexMap (Subtype.val : W → M)
        contMDiff_subtypeVal) (ModuleCat.of ℝ ℝ)).f k c') :
    relativeDeRhamCohomology I W (k + 1 : ℕ) →ₗ[ℝ] ℝ where
  toFun x := cycleIntegral I W k c c' (classRep I W k x)
  map_add' x y := by
    rw [← map_add]
    exact cycleIntegral_eq_of_homologyπ_eq I W k hc (by
      rw [map_add, homologyπ_classRep, homologyπ_classRep, homologyπ_classRep])
  map_smul' r x := by
    rw [RingHom.id_apply, ← map_smul]
    exact cycleIntegral_eq_of_homologyπ_eq I W k hc (by
      rw [map_smul, homologyπ_classRep, homologyπ_classRep])

/-- The integral of the class of a relative cocycle `(α, β)` over `(c, c')` is
`∫_c α - ∫_{c'} β`. -/
theorem integral_mk (k : ℕ) {c : 𝒮[M].X (k + 1)} {c' : 𝒮[W].X k}
    (hc : 𝒮[M].d (k + 1) k c =
      (SSet.chainComplexMap (smoothSingularSubcomplexMap (Subtype.val : W → M)
        contMDiff_subtypeVal) (ModuleCat.of ℝ ℝ)).f k c')
    (z : cocycles I W k) :
    integral I W k hc (mk I W k z) =
      (integrationCochain z.val.1.val).hom c - (integrationCochain z.val.2.val).hom c' := by
  obtain ⟨⟨α, β⟩, hz⟩ := z
  rw [integral, LinearMap.coe_mk, AddHom.coe_mk,
    cycleIntegral_eq_of_homologyπ_eq I W k hc
      ((homologyπ_classRep I W k _).trans (mk_apply I W k _)),
    cycleIntegral, LinearMap.comp_apply, LinearMap.comp_apply]
  rw [show ∀ x m hm hx, ((relativeDeRhamComplex I W).iCycles (k + 1 : ℕ)).hom
      ((relativeDeRhamComplex I W).moduleCatCyclesMk x m hm hx) = x from
    fun x m hm hx ↦ iCycles_moduleCatCyclesMk (x := x) (m := m) (hm := hm) (hx := hx)]
  exact relativeSmoothCochainComplex.eval_relativeDeRhamIntegration_f_coord_symm I W k c c' α β

end relativeDeRhamCohomology

end TauCeti
