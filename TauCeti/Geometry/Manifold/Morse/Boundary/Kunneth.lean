/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Boundary.ChainComplex
public import TauCeti.Geometry.Manifold.Morse.Boundary.Prod.Basic
public import TauCeti.Algebra.Homology.Monoidal.Tensor.Differential
public import TauCeti.Algebra.Homology.Monoidal.Homology.Kunneth.Basic
public import TauCeti.Algebra.Homology.Semisimple
public import TauCeti.Algebra.Module.ZMod.Sign

/-!
# The Künneth theorem for mod-two Morse homology

Let `f` be a Morse function on a compact boundaryless manifold `M` with a Morse–Smale adapted
pseudo-gradient `X`, and likewise `g`, `Y` on `N`. The separated sum `f ∘ Prod.fst + g ∘ Prod.snd`
is a Morse function on `M × N` and the product field `(X, Y)` is a Morse–Smale pseudo-gradient
adapted to it, so `M × N` has a mod-two Morse chain complex
(`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.morseComplex`). This file identifies it with the
tensor product of the mod-two Morse chain complexes of `M` and of `N`, and deduces the Künneth
formula for mod-two Morse homology.

The chain-level statement
`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.morseChainProdEquiv_comp_morseBoundary` says that,
on all Morse chains at once, the pair `(p, q)` of critical points corresponds to `p ⊗ q` and the
boundary of the product to `∂ ⊗ 1 + 1 ⊗ ∂`. Here this is graded by the Morse index: the critical
point `(p, q)` has index `ind p + ind q`, so in degree `n` the comparison sends the summand
`Cₚ(f) ⊗ C_q(g)` with `p + q = n` of the tensor product complex into the chains
`Cₙ(f ∘ Prod.fst + g ∘ Prod.snd)` of the product by `p ⊗ q ↦ (p, q)`. These maps assemble into
an isomorphism of chain complexes
(`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.morseComplexTensorIso`); over `ZMod 2` the Koszul
sign `(-1)ᵖ` of the tensor product differential is `1` (`TauCeti.ZModModule.neg_one_pow_zsmul`).
The construction follows `TauCeti.koszulComplex.tensorIso` in
`TauCeti.RingTheory.KoszulComplex.Tensor`: summand-wise comparison maps out of the tensor product
complex, assembled degreewise by `HomologicalComplex.Hom.isoOfComponents`, with an evaluation lemma
on `p ⊗ q`.

Over the field `ZMod 2` the algebraic Künneth theorem
(`HomologicalComplex.isIso_homologyKunneth_of_isSplitMono_of_isSplitEpi`) then gives the
**Künneth isomorphism**

`⨁_{p + q = n} Hₚ(f, X) ⊗ H_q(g, Y) ≅ Hₙ(f ∘ Prod.fst + g ∘ Prod.snd, (X, Y))`,

induced by the homology cross product
(`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.morseHomologyKunnethIso`), and the formula
`bₙ(M × N) = ∑_{p + q = n} bₚ(M) b_q(N)` for the dimensions of the mod-two Morse homology
(`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.finrank_homology_morseComplex_prod`), read off from
the Künneth isomorphism by `CategoryTheory.GradedObject.Monoidal.finrank_tensorObj` as in the
singular-homology count `TopCat.finrank_singularHomology_tensor`.

The manifolds are taken in `Type`, the universe of the coefficient ring `ZMod 2`, where Mathlib's
category of modules is monoidal.

## Main declarations

In the namespace `TauCeti.IsAdaptedPseudoGradient.IsMorseSmale`:

* `morseComplexTensorIso`: the tensor product of the mod-two Morse chain complexes of `M` and `N`
  is isomorphic to the mod-two Morse chain complex of `M × N`, with
  `morseComplexTensorIso_hom_f_ιTensorObj_single_tmul_single` computing it on `p ⊗ q`.
* `morseHomologyKunnethIso`: the Künneth isomorphism for mod-two Morse homology.
* `finrank_homology_morseComplex_prod`: the dimensions of the mod-two Morse homology of `M × N`.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §3, Exercise 2 (the Morse complex of a product is the tensor
  product of the Morse complexes, and the Künneth theorem for Morse homology).
* C. Weibel, *An Introduction to Homological Algebra*, Theorem 3.6.3 (the Künneth formula).
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory HomologicalComplex Module
open scoped ContDiff Manifold TensorProduct

namespace TauCeti

namespace IsAdaptedPseudoGradient

namespace IsMorseSmale

variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {M N : Type} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M] [TopologicalSpace N] [ChartedSpace E' N]
  [IsManifold 𝓘(ℝ, E') ∞ N] [CompactSpace N] [T2Space N]
  {f : M → ℝ} {g : N → ℝ} {X : (z : M) → TangentSpace 𝓘(ℝ, E) z}
  {Y : (z : N) → TangentSpace 𝓘(ℝ, E') z}
  {hX : IsAdaptedPseudoGradient f X} {hY : IsAdaptedPseudoGradient g Y}
  (hXs : hX.IsMorseSmale) (hYs : hY.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)
  (hg : IsMorse 𝓘(ℝ, E') g)

attribute [local instance low] chartedSpaceProd

attribute [local instance] isManifold_chartedSpaceProd

/-- The critical points of `f` of index `p`. -/
local notation "ℐ₁[" p "]" => {x : criticalPoints 𝓘(ℝ, E) f // manifoldMorseIndex 𝓘(ℝ, E) f x = p}

/-- The critical points of `g` of index `q`. -/
local notation "ℐ₂[" q "]" =>
  {y : criticalPoints 𝓘(ℝ, E') g // manifoldMorseIndex 𝓘(ℝ, E') g y = q}

/-- The critical points of the separated sum of index `n`. -/
local notation "ℐ[" n "]" => {P : criticalPoints 𝓘(ℝ, E × E') (f ∘ Prod.fst + g ∘ Prod.snd) //
  manifoldMorseIndex 𝓘(ℝ, E × E') (f ∘ Prod.fst + g ∘ Prod.snd) (P : M × N) = n}

/-- The critical points of the separated sum are the pairs of critical points. -/
local notation "eFG" =>
  criticalPointsCompFstAddCompSndEquiv f g (IsAdaptedPseudoGradient.mdifferentiable hX)
    (IsAdaptedPseudoGradient.mdifferentiable hY)

/-- The mod-two Morse complex of `(f, X)`. -/
local notation "𝒦" => morseComplex hXs hf

/-- The mod-two Morse complex of `(g, Y)`. -/
local notation "ℒ" => morseComplex hYs hg

/-- The mod-two Morse complex of the separated sum with the product field. -/
local notation "𝒫" =>
  morseComplex (IsMorseSmale.prod hXs hYs) (IsMorse.comp_fst_add_comp_snd_chartedSpaceProd hf hg)

/-- The term of degree `n` of the Morse complex of the separated sum, written without the field. The
comparison maps are stated with this target: it is the term `(𝒫).X n` by definition, but terms
mentioning the product field cannot be rewritten, since its tangent spaces are those of the product
model `𝓘(ℝ, E).prod 𝓘(ℝ, E')`. -/
local notation "𝒞[" n "]" => ModuleCat.of (ZMod 2) (ℐ[n] →₀ ZMod 2)

omit [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [T2Space M] [IsManifold 𝓘(ℝ, E') ∞ N]
  [CompactSpace N] [T2Space N] in
include hf hg in
/-- The Morse index of a critical point `(p, q)` of the separated sum is `ind p + ind q`. -/
private theorem morseIndex_prod (P : criticalPoints 𝓘(ℝ, E × E') (f ∘ Prod.fst + g ∘ Prod.snd)) :
    manifoldMorseIndex 𝓘(ℝ, E × E') (f ∘ Prod.fst + g ∘ Prod.snd) (P : M × N) =
      manifoldMorseIndex 𝓘(ℝ, E) f (P : M × N).1 + manifoldMorseIndex 𝓘(ℝ, E') g (P : M × N).2 :=
  manifoldMorseIndex_comp_fst_add_comp_snd_chartedSpaceProd
    ((hf.contMDiff _).of_le (by norm_num)) ((hg.contMDiff _).of_le (by norm_num))

variable {hXs hYs hf hg}

/-! ### The comparison in each degree -/

variable (hf hg) in
/-- The critical point `(p, q)` of the separated sum, of index `n` when `ind p + ind q = n`. -/
private def prodPoint {p q n : ℕ} (h : p + q = n) (a : ℐ₁[p]) (b : ℐ₂[q]) : ℐ[n] :=
  ⟨(eFG).symm (a.val, b.val), by
    rw [morseIndex_prod hf hg, coe_criticalPointsCompFstAddCompSndEquiv_symm, a.property,
      b.property, h]⟩

variable (hf hg) in
/-- The comparison map on the summand `Cₚ(f) ⊗ C_q(g)`, sending `p ⊗ q` to `(p, q)`. -/
private def toProdLinear (p q n : ℕ) (h : p + q = n) :
    ((ℐ₁[p] →₀ ZMod 2) ⊗[ZMod 2] (ℐ₂[q] →₀ ZMod 2)) →ₗ[ZMod 2] (ℐ[n] →₀ ZMod 2) :=
  Finsupp.lmapDomain (ZMod 2) (ZMod 2) (fun ab ↦ prodPoint (hX := hX) (hY := hY) hf hg h ab.1 ab.2)
    ∘ₗ (finsuppTensorFinsupp' (ZMod 2) _ _).toLinearMap

variable (hXs hYs hf hg) in
/-- The comparison map from the tensor product of the Morse complexes to the Morse complex of the
product in degree `n`. -/
private def toProd (n : ℕ) : (𝒦 ⊗ ℒ).X n ⟶ 𝒞[n] :=
  mapBifunctorDesc fun p q h ↦ ModuleCat.ofHom (toProdLinear (hX := hX) (hY := hY) hf hg p q n h)

private theorem toProd_ιTensorObj_apply (p q n : ℕ) (h : p + q = n)
    (z : (ℐ₁[p] →₀ ZMod 2) ⊗[ZMod 2] (ℐ₂[q] →₀ ZMod 2)) :
    (toProd hXs hYs hf hg n).hom ((ιTensorObj 𝒦 ℒ p q n h).hom z) =
      toProdLinear (hX := hX) (hY := hY) hf hg p q n h z :=
  congr($(ι_mapBifunctorDesc (K₁ := 𝒦) (K₂ := ℒ) (F := curriedTensor (ModuleCat (ZMod 2)))
    (c := ComplexShape.down ℕ)
    (fun p q h ↦ ModuleCat.ofHom (toProdLinear (hX := hX) (hY := hY) hf hg p q n h)) p q h).hom z)

omit [CompactSpace M] [T2Space M] [CompactSpace N] [T2Space N] in
private theorem toProdLinear_single_tmul_single {p q n : ℕ} (h : p + q = n) (a : ℐ₁[p]) (b : ℐ₂[q])
    (r s : ZMod 2) :
    toProdLinear (hX := hX) (hY := hY) hf hg p q n h (Finsupp.single a r ⊗ₜ Finsupp.single b s) =
      Finsupp.single (prodPoint (hX := hX) (hY := hY) hf hg h a b) (r * s) := by
  simp [toProdLinear, finsuppTensorFinsupp'_single_tmul_single]

variable (hXs hYs hf hg) in
/-- The element `p ⊗ q` of the tensor product complex attached to a critical point `(p, q)` of
index `n` of the separated sum. -/
private def prodTensor {n : ℕ} (P : ℐ[n]) : (𝒦 ⊗ ℒ).X n :=
  (ιTensorObj 𝒦 ℒ _ _ n ((morseIndex_prod hf hg P.val).symm.trans P.property)).hom
    (Finsupp.single (⟨(eFG P.val).1, by rw [coe_criticalPointsCompFstAddCompSndEquiv_fst]⟩ :
        ℐ₁[manifoldMorseIndex 𝓘(ℝ, E) f (P.val : M × N).1]) (1 : ZMod 2) ⊗ₜ
      Finsupp.single (⟨(eFG P.val).2, by rw [coe_criticalPointsCompFstAddCompSndEquiv_snd]⟩ :
        ℐ₂[manifoldMorseIndex 𝓘(ℝ, E') g (P.val : M × N).2]) (1 : ZMod 2))

variable (hXs hYs hf hg) in
/-- The comparison map from the Morse complex of the product to the tensor product of the Morse
complexes in degree `n`, sending `(p, q)` to `p ⊗ q`. -/
private def fromProd (n : ℕ) : 𝒞[n] ⟶ (𝒦 ⊗ ℒ).X n :=
  ModuleCat.ofHom <| Finsupp.linearCombination (ZMod 2) (prodTensor hXs hYs hf hg (n := n))

private theorem fromProd_single {n : ℕ} (P : ℐ[n]) :
    (fromProd hXs hYs hf hg n).hom (Finsupp.single P 1) = prodTensor hXs hYs hf hg P := by
  -- `fromProd` is `ModuleCat.ofHom` of a linear map whose source is only definitionally the term
  -- of the Morse complex, so `ModuleCat.hom_ofHom` does not rewrite.
  change Finsupp.linearCombination (ZMod 2) (prodTensor hXs hYs hf hg) (Finsupp.single P 1) = _
  rw [Finsupp.linearCombination_single, one_smul]

/-- Morphisms out of a summand `Cₚ(f) ⊗ C_q(g)` of the tensor product complex agree once they agree
on the tensor products `p ⊗ q` of critical points. -/
private theorem summand_hom_ext {p q : ℕ} {Z : ModuleCat.{0} (ZMod 2)}
    {φ ψ : (𝒦).X p ⊗ (ℒ).X q ⟶ Z}
    (h : ∀ (a : ℐ₁[p]) (b : ℐ₂[q]),
      φ.hom (Finsupp.single a 1 ⊗ₜ Finsupp.single b 1 :
          (ℐ₁[p] →₀ ZMod 2) ⊗[ZMod 2] (ℐ₂[q] →₀ ZMod 2)) =
        ψ.hom (Finsupp.single a 1 ⊗ₜ Finsupp.single b 1 :
          (ℐ₁[p] →₀ ZMod 2) ⊗[ZMod 2] (ℐ₂[q] →₀ ZMod 2))) :
    φ = ψ :=
  ModuleCat.hom_ext <| TensorProduct.ext <| Finsupp.lhom_ext' fun a ↦ LinearMap.ext_ring <|
    Finsupp.lhom_ext' fun b ↦ LinearMap.ext_ring (h a b)

/-- Morphisms out of the tensor product complex in degree `n` agree once they agree on the tensor
products `p ⊗ q` of critical points with `ind p + ind q = n`. -/
private theorem tensor_hom_ext {n : ℕ} {Z : ModuleCat.{0} (ZMod 2)} {φ ψ : (𝒦 ⊗ ℒ).X n ⟶ Z}
    (h : ∀ (p q : ℕ) (hpq : p + q = n) (a : ℐ₁[p]) (b : ℐ₂[q]),
      φ.hom ((ιTensorObj 𝒦 ℒ p q n hpq).hom (Finsupp.single a 1 ⊗ₜ Finsupp.single b 1 :
          (ℐ₁[p] →₀ ZMod 2) ⊗[ZMod 2] (ℐ₂[q] →₀ ZMod 2))) =
        ψ.hom ((ιTensorObj 𝒦 ℒ p q n hpq).hom (Finsupp.single a 1 ⊗ₜ Finsupp.single b 1 :
          (ℐ₁[p] →₀ ZMod 2) ⊗[ZMod 2] (ℐ₂[q] →₀ ZMod 2)))) :
    φ = ψ :=
  mapBifunctor.hom_ext fun p q hpq ↦ summand_hom_ext fun a b ↦ h p q hpq a b

/-- The summand inclusions of the tensor product complex agree on `p ⊗ q` whatever the names of
the degrees of `p` and `q`. -/
private theorem ιTensorObj_single_tmul_single_congr {p q p' q' n : ℕ} (hp : p' = p) (hq : q' = q)
    (h : p + q = n) (h' : p' + q' = n) (a : ℐ₁[p]) (a' : ℐ₁[p']) (b : ℐ₂[q]) (b' : ℐ₂[q'])
    (ha : a'.val = a.val) (hb : b'.val = b.val) :
    (ιTensorObj 𝒦 ℒ p' q' n h').hom (Finsupp.single a' (1 : ZMod 2) ⊗ₜ Finsupp.single b' 1) =
      (ιTensorObj 𝒦 ℒ p q n h).hom (Finsupp.single a (1 : ZMod 2) ⊗ₜ Finsupp.single b 1) := by
  subst hp hq
  obtain rfl : a' = a := Subtype.ext ha
  obtain rfl : b' = b := Subtype.ext hb
  rfl

variable (hXs hYs hf hg) in
/-- The comparison in degree `n` is an isomorphism. -/
private def degreeIso (n : ℕ) : (𝒦 ⊗ ℒ).X n ≅ 𝒞[n] where
  hom := toProd hXs hYs hf hg n
  inv := fromProd hXs hYs hf hg n
  hom_inv_id := tensor_hom_ext fun p q h a b ↦ by
    rw [ModuleCat.hom_comp, LinearMap.comp_apply, toProd_ιTensorObj_apply,
      toProdLinear_single_tmul_single, mul_one, fromProd_single, ModuleCat.hom_id,
      LinearMap.id_apply, prodTensor]
    refine ιTensorObj_single_tmul_single_congr ?_ ?_ h _ a _ b _ ?_ ?_
    · simp [prodPoint, a.property]
    · simp [prodPoint, b.property]
    · exact congrArg Prod.fst ((eFG).apply_symm_apply (a.val, b.val))
    · exact congrArg Prod.snd ((eFG).apply_symm_apply (a.val, b.val))
  inv_hom_id := by
    refine ModuleCat.hom_ext <| Finsupp.lhom_ext' fun P ↦ LinearMap.ext_ring ?_
    -- The extensionality lemmas leave the composite in the form of linear maps out of the free
    -- module, which is the term of degree `n` only by definition.
    change (toProd hXs hYs hf hg n).hom ((fromProd hXs hYs hf hg n).hom (Finsupp.single P 1)) =
      Finsupp.single P 1
    rw [fromProd_single]
    refine (toProd_ιTensorObj_apply _ _ _ _ _).trans <|
      (toProdLinear_single_tmul_single _ _ _ _ _).trans ?_
    rw [mul_one]
    exact congrArg (Finsupp.single · 1) (Subtype.ext ((eFG).symm_apply_apply P.val))

/-! ### The comparison commutes with the differentials -/

variable (hX hY) in
/-- The graded Morse chains of index `n` of the product, included into all Morse chains of the
product and read as the tensor product of the Morse chains of the factors. -/
private def totalChains (n : ℕ) :
    (ℐ[n] →₀ ZMod 2) →ₗ[ZMod 2]
      (criticalPoints 𝓘(ℝ, E) f →₀ ZMod 2) ⊗[ZMod 2] (criticalPoints 𝓘(ℝ, E') g →₀ ZMod 2) :=
  (morseChainProdEquiv f g (ZMod 2) hX.mdifferentiable hY.mdifferentiable).toLinearMap ∘ₗ
    Finsupp.lmapDomain (ZMod 2) (ZMod 2) Subtype.val

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [CompactSpace M] [T2Space M]
  [CompactSpace N] [T2Space N] in
private theorem totalChains_injective (n : ℕ) : Function.Injective (totalChains hX hY n) :=
  (LinearEquiv.injective _).comp (Finsupp.mapDomain_injective Subtype.val_injective)

omit [CompactSpace M] [T2Space M] [CompactSpace N] [T2Space N] in
private theorem totalChains_toProdLinear (p q n : ℕ) (h : p + q = n)
    (z : (ℐ₁[p] →₀ ZMod 2) ⊗[ZMod 2] (ℐ₂[q] →₀ ZMod 2)) :
    totalChains hX hY n (toProdLinear (hX := hX) (hY := hY) hf hg p q n h z) =
      TensorProduct.map (Finsupp.lmapDomain (ZMod 2) (ZMod 2) Subtype.val)
        (Finsupp.lmapDomain (ZMod 2) (ZMod 2) Subtype.val) z := by
  have : totalChains hX hY n ∘ₗ toProdLinear (hX := hX) (hY := hY) hf hg p q n h =
      TensorProduct.map (Finsupp.lmapDomain (ZMod 2) (ZMod 2) Subtype.val)
        (Finsupp.lmapDomain (ZMod 2) (ZMod 2) Subtype.val) := by
    refine TensorProduct.ext <| Finsupp.lhom_ext' fun a ↦ LinearMap.ext_ring <|
      Finsupp.lhom_ext' fun b ↦ LinearMap.ext_ring ?_
    simp only [totalChains, LinearMap.compr₂ₛₗ_apply, TensorProduct.mk_apply, LinearMap.coe_comp,
      LinearEquiv.coe_coe, Function.comp_apply, Finsupp.lsingle_apply,
      toProdLinear_single_tmul_single, mul_one, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
      TensorProduct.map_tmul]
    exact morseChainProdEquiv_single (R := ZMod 2) a.val b.val 1
  exact LinearMap.congr_fun this z

/-- Read on all Morse chains, the Morse boundary of the product is `∂ ⊗ 1 + 1 ⊗ ∂`. -/
private theorem totalChains_d (n : ℕ) (w : ℐ[n + 1] →₀ ZMod 2) :
    totalChains hX hY n (((𝒫).d (n + 1) n).hom w) =
      ((hXs.morseBoundary hf).rTensor (criticalPoints 𝓘(ℝ, E') g →₀ ZMod 2) +
          (hYs.morseBoundary hg).lTensor (criticalPoints 𝓘(ℝ, E) f →₀ ZMod 2))
        (totalChains hX hY (n + 1) w) := by
  refine (congrArg (totalChains hX hY n)
    (morseComplex_d_apply (hXs.prod hYs) (hf.comp_fst_add_comp_snd_chartedSpaceProd hg) n w)).trans
      ?_
  simp only [totalChains, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    Finsupp.lmapDomain_apply]
  exact (congrArg _ (mapDomain_morseBoundaryAt (hXs.prod hYs)
    (hf.comp_fst_add_comp_snd_chartedSpaceProd hg) w)).trans
    (LinearMap.congr_fun (morseChainProdEquiv_comp_morseBoundary hXs hYs hf hg) _)

/-- Read on all Morse chains, the comparison map carries `∂ x ⊗ y` to `∂ x ⊗ y`. -/
private theorem totalChains_toProd_whiskerRight (r q n : ℕ) (h : r + q = n)
    (x : ℐ₁[r + 1] →₀ ZMod 2) (y : ℐ₂[q] →₀ ZMod 2) :
    totalChains hX hY n ((toProd hXs hYs hf hg n).hom ((ιTensorObj 𝒦 ℒ r q n h).hom
        (((𝒦).d (r + 1) r ▷ (ℒ).X q).hom
          (x ⊗ₜ y : (ℐ₁[r + 1] →₀ ZMod 2) ⊗[ZMod 2] (ℐ₂[q] →₀ ZMod 2))))) =
      hXs.morseBoundary hf (x.mapDomain Subtype.val) ⊗ₜ y.mapDomain Subtype.val := by
  -- The chains `x` and `y` are elements of the free modules on critical points, which are the terms
  -- of `𝒦` and `ℒ` only by definition. The lemmas used here state chains at one or the other of
  -- these types (`morseComplex_d_apply` at the free module, `whiskerRight_apply` at the term of the
  -- complex), so with either type for `x` some `rw` or `simp only` step fails to match or produces
  -- an ill-typed motive. The steps are therefore chained with `congrArg` and `Eq.trans`, which
  -- compare these types up to unfolding.
  refine (congrArg (fun z ↦ totalChains hX hY n ((toProd hXs hYs hf hg n).hom
    ((ιTensorObj 𝒦 ℒ r q n h).hom z)))
      ((ModuleCat.MonoidalCategory.whiskerRight_apply _ _ _ _).trans
        (congrArg (· ⊗ₜ[ZMod 2] y) (morseComplex_d_apply hXs hf r x)))).trans ?_
  refine (congrArg (totalChains hX hY n) (toProd_ιTensorObj_apply r q n h _)).trans <|
    (totalChains_toProdLinear r q n h _).trans <| (TensorProduct.map_tmul _ _ _ _).trans ?_
  exact congrArg (· ⊗ₜ[ZMod 2] _) (mapDomain_morseBoundaryAt hXs hf x)

/-- Read on all Morse chains, the comparison map carries `x ⊗ ∂ y` to `x ⊗ ∂ y`. -/
private theorem totalChains_toProd_whiskerLeft (p s n : ℕ) (h : p + s = n)
    (x : ℐ₁[p] →₀ ZMod 2) (y : ℐ₂[s + 1] →₀ ZMod 2) :
    totalChains hX hY n ((toProd hXs hYs hf hg n).hom ((ιTensorObj 𝒦 ℒ p s n h).hom
        (((𝒦).X p ◁ (ℒ).d (s + 1) s).hom
          (x ⊗ₜ y : (ℐ₁[p] →₀ ZMod 2) ⊗[ZMod 2] (ℐ₂[s + 1] →₀ ZMod 2))))) =
      x.mapDomain Subtype.val ⊗ₜ hYs.morseBoundary hg (y.mapDomain Subtype.val) := by
  -- As in `totalChains_toProd_whiskerRight`, the chains live at two definitionally equal types, so
  -- the steps are chained with `congrArg` and `Eq.trans` rather than rewritten.
  refine (congrArg (fun z ↦ totalChains hX hY n ((toProd hXs hYs hf hg n).hom
    ((ιTensorObj 𝒦 ℒ p s n h).hom z)))
      ((ModuleCat.MonoidalCategory.whiskerLeft_apply _ _ _ _).trans
        (congrArg (x ⊗ₜ[ZMod 2] ·) (morseComplex_d_apply hYs hg s y)))).trans ?_
  refine (congrArg (totalChains hX hY n) (toProd_ιTensorObj_apply p s n h _)).trans <|
    (totalChains_toProdLinear p s n h _).trans <| (TensorProduct.map_tmul _ _ _ _).trans ?_
  exact congrArg (_ ⊗ₜ[ZMod 2] ·) (mapDomain_morseBoundaryAt hYs hg y)

/-- Read on all Morse chains, the comparison map carries the differential of the tensor product
complex on `p ⊗ q` to `∂ p ⊗ q + p ⊗ ∂ q`; over `ZMod 2` the Koszul sign is `1`, and a term in
which a critical point of index zero is differentiated vanishes on both sides. -/
private theorem totalChains_toProd_d (p q n : ℕ) (h : p + q = n + 1) (a : ℐ₁[p]) (b : ℐ₂[q]) :
    totalChains hX hY n ((ιTensorObj 𝒦 ℒ p q (n + 1) h ≫ (𝒦 ⊗ ℒ).d (n + 1) n ≫
        toProd hXs hYs hf hg n).hom (Finsupp.single a 1 ⊗ₜ Finsupp.single b 1 :
          (ℐ₁[p] →₀ ZMod 2) ⊗[ZMod 2] (ℐ₂[q] →₀ ZMod 2))) =
      hXs.morseBoundary hf (Finsupp.single a.val 1) ⊗ₜ Finsupp.single b.val 1 +
        Finsupp.single a.val 1 ⊗ₜ hYs.morseBoundary hg (Finsupp.single b.val 1) := by
  have hd : (𝒦 ⊗ ℒ).d (n + 1) n =
      mapBifunctor.D₁ 𝒦 ℒ (curriedTensor (ModuleCat.{0} (ZMod 2))) (ComplexShape.down ℕ) (n + 1) n +
        mapBifunctor.D₂ 𝒦 ℒ (curriedTensor (ModuleCat.{0} (ZMod 2))) (ComplexShape.down ℕ)
          (n + 1) n :=
    mapBifunctor.d_eq _ _ _ _ _ _
  rw [hd, Preadditive.add_comp, Preadditive.comp_add]
  rcases p with _ | r <;> rcases q with _ | s
  · omega
  · obtain rfl : s = n := by omega
    rw [ChainComplex.ιTensorObj_D₁_zero_assoc, Limits.zero_comp, zero_add,
      ChainComplex.ιTensorObj_D₂_succ_assoc, ZModModule.neg_one_pow_zsmul]
    refine (totalChains_toProd_whiskerLeft 0 s s (by omega) _ _).trans ?_
    rw [Finsupp.mapDomain_single, Finsupp.mapDomain_single, ← Finsupp.mapDomain_single,
      morseBoundary_mapDomain_eq_zero_of_index_zero, TensorProduct.zero_tmul, zero_add]
  · obtain rfl : r = n := by omega
    rw [ChainComplex.ιTensorObj_D₂_zero_assoc, Limits.zero_comp, add_zero,
      ChainComplex.ιTensorObj_D₁_succ_assoc]
    refine (totalChains_toProd_whiskerRight r 0 r (by omega) _ _).trans ?_
    rw [Finsupp.mapDomain_single, Finsupp.mapDomain_single,
      ← Finsupp.mapDomain_single (f := Subtype.val) (a := b),
      morseBoundary_mapDomain_eq_zero_of_index_zero, TensorProduct.tmul_zero, add_zero]
  · rw [ChainComplex.ιTensorObj_D₁_succ_assoc, ChainComplex.ιTensorObj_D₂_succ_assoc,
      ZModModule.neg_one_pow_zsmul, ModuleCat.hom_add]
    -- The two terms are rewritten separately by `congrArg₂`: the whiskering lemmas apply to them
    -- only up to unfolding the terms of the Morse complexes
    -- (see `totalChains_toProd_whiskerRight`).
    refine (congrArg (totalChains hX hY n) (LinearMap.add_apply _ _ _)).trans <|
      (map_add _ _ _).trans <| congrArg₂ (· + ·)
        ((totalChains_toProd_whiskerRight r (s + 1) n (by omega) _ _).trans ?_)
        ((totalChains_toProd_whiskerLeft (r + 1) s n (by omega) _ _).trans ?_) <;>
    rw [Finsupp.mapDomain_single, Finsupp.mapDomain_single]

/-- The comparison maps commute with the differentials. -/
private theorem toProd_comm (n : ℕ) :
    toProd hXs hYs hf hg (n + 1) ≫ (𝒫).d (n + 1) n =
      (𝒦 ⊗ ℒ).d (n + 1) n ≫ toProd hXs hYs hf hg n := by
  refine tensor_hom_ext fun p q h a b ↦ totalChains_injective (hX := hX) (hY := hY) n ?_
  refine (totalChains_d (hXs := hXs) (hYs := hYs) (hf := hf) (hg := hg) n _).trans <|
    Eq.trans ?_ (totalChains_toProd_d p q n h a b).symm
  -- `toProd_ιTensorObj_apply` states the summand at the tensor product of the free modules on
  -- critical points, which is the term of `𝒦 ⊗ ℒ` only by definition, so it is applied under
  -- `congrArg` rather than rewritten (see `totalChains_toProd_whiskerRight`).
  refine (congrArg _ ((congrArg (totalChains hX hY (n + 1))
    (toProd_ιTensorObj_apply p q (n + 1) h _)).trans <|
      (totalChains_toProdLinear p q (n + 1) h _).trans (TensorProduct.map_tmul _ _ _ _))).trans ?_
  simp [Finsupp.mapDomain_single]

/-! ### The Künneth theorem -/

variable (hXs hYs hf hg) in
/-- **The mod-two Morse complex of a product is the tensor product of the Morse complexes.** For
Morse–Smale pseudo-gradients `X` on `M` and `Y` on `N`, adapted to Morse functions `f` and `g`, the
tensor product of the mod-two Morse chain complexes of `(f, X)` and `(g, Y)` is isomorphic to the
mod-two Morse chain complex of the separated sum `f ∘ Prod.fst + g ∘ Prod.snd` with the product
field `(X, Y)`. In degree `n` it sends `p ⊗ q`, for critical points `p` and `q` with
`ind p + ind q = n`, to the critical point `(p, q)`
(`morseComplexTensorIso_hom_f_ιTensorObj_single_tmul_single`). -/
def morseComplexTensorIso : 𝒦 ⊗ ℒ ≅ 𝒫 :=
  Hom.isoOfComponents (degreeIso hXs hYs hf hg) <| by
    rintro _ n rfl
    exact toProd_comm n

/-- `morseComplexTensorIso` sends `p ⊗ q` to the critical point `(p, q)` of the separated sum,
read among all Morse chains of `M × N`. -/
theorem morseComplexTensorIso_hom_f_ιTensorObj_single_tmul_single {p q n : ℕ} (h : p + q = n)
    (a : ℐ₁[p]) (b : ℐ₂[q]) :
    Finsupp.mapDomain Subtype.val
        ((((morseComplexTensorIso hXs hYs hf hg).hom.f n).hom ((ιTensorObj 𝒦 ℒ p q n h).hom
          (Finsupp.single a 1 ⊗ₜ Finsupp.single b 1 :
            (ℐ₁[p] →₀ ZMod 2) ⊗[ZMod 2] (ℐ₂[q] →₀ ZMod 2)))) : ℐ[n] →₀ ZMod 2) =
      Finsupp.single ((eFG).symm (a.val, b.val)) 1 :=
  (congrArg (Finsupp.mapDomain Subtype.val) ((toProd_ιTensorObj_apply p q n h _).trans
    ((toProdLinear_single_tmul_single h a b 1 1).trans (by rw [mul_one])))).trans
    (Finsupp.mapDomain_single ..)

variable (hXs hYs hf hg) in
/-- **The Künneth isomorphism for mod-two Morse homology**
`⨁_{p + q = n} Hₚ(f, X) ⊗ H_q(g, Y) ≅ Hₙ(f ∘ Prod.fst + g ∘ Prod.snd, (X, Y))`. It is the
algebraic Künneth map of the Morse complexes of `M` and `N`, induced by the homology cross product,
which is an isomorphism over the field `ZMod 2`, followed by the map induced on homology by the
isomorphism `morseComplexTensorIso` of chain complexes. -/
def morseHomologyKunnethIso (n : ℕ) :
    GradedObject.Monoidal.tensorObj (fun p ↦ (𝒦).homology p) (fun q ↦ (ℒ).homology q) n ≅
      (𝒫).homology n :=
  asIso (homologyKunneth 𝒦 ℒ n) ≪≫
    (homologyFunctor _ _ n).mapIso (morseComplexTensorIso hXs hYs hf hg)

/-- On the summand `Hₚ(f, X) ⊗ H_q(g, Y)`, the Künneth isomorphism is the homology cross product
followed by the map induced by `morseComplexTensorIso`. -/
@[reassoc (attr := simp)]
theorem ι_morseHomologyKunnethIso_hom (p q n : ℕ) (h : p + q = n) :
    GradedObject.Monoidal.ιTensorObj (fun p ↦ (𝒦).homology p) (fun q ↦ (ℒ).homology q) p q n h ≫
        (morseHomologyKunnethIso hXs hYs hf hg n).hom =
      homologyCross 𝒦 ℒ p q n h ≫ homologyMap (morseComplexTensorIso hXs hYs hf hg).hom n :=
  -- The Künneth isomorphism is by definition the Künneth map followed by the induced map on
  -- homology. Rewriting it is blocked by the product field, so the defining equation is applied
  -- up to unfolding.
  ι_homologyKunneth_assoc 𝒦 ℒ n p q h _

/-- **The Künneth formula for the dimensions of mod-two Morse homology.** The mod-two Morse
homology of `M × N` in degree `n`, for the separated sum `f ∘ Prod.fst + g ∘ Prod.snd` and the
product field `(X, Y)`, has dimension `∑_{p + q = n} bₚ(f, X) b_q(g, Y)`, where `bₚ` is the
dimension of the mod-two Morse homology in degree `p`. -/
theorem finrank_homology_morseComplex_prod (n : ℕ) :
    finrank (ZMod 2) ((𝒫).homology n) =
      ∑ x ∈ Finset.antidiagonal n,
        finrank (ZMod 2) ((𝒦).homology x.1) * finrank (ZMod 2) ((ℒ).homology x.2) :=
  (morseHomologyKunnethIso hXs hYs hf hg n).toLinearEquiv.finrank_eq.symm.trans
    (GradedObject.Monoidal.finrank_tensorObj _ _ n)

end IsMorseSmale

end IsAdaptedPseudoGradient

end TauCeti
