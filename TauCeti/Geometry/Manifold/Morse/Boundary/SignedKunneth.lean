/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Boundary.SignedChainComplex
public import TauCeti.Geometry.Manifold.Morse.Boundary.Prod.Integral
public import TauCeti.Algebra.Homology.Monoidal.Tensor.Differential
public import TauCeti.Algebra.Homology.Monoidal.Homology.Kunneth.Sequence.Basic
public import TauCeti.Algebra.Homology.PrincipalIdealRing

/-!
# The Künneth theorem for integral Morse homology

Let `f` be a Morse function on a compact boundaryless manifold `M` with a Morse–Smale adapted
pseudo-gradient `X` and orientation data `𝔬`, and likewise `g`, `Y`, `𝔬'` on `N`. With the product
orientation data `𝔬.prod 𝔬'` (the unstable manifold of `p` followed by that of `q`), the integral
Morse boundary of the separated sum `f ∘ Prod.fst + g ∘ Prod.snd` for the product field `(X, Y)`
is `∂ (p ⊗ q) = ∂ p ⊗ q + (-1) ^ ind p p ⊗ ∂ q`
(`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.morseChainProdEquiv_comp_signedMorseBoundary`), and
it squares to zero when the boundaries of the factors do
(`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.signedMorseBoundary_comp_signedMorseBoundary_prod`).
So for every commutative ring `R` over which the integral Morse complexes `𝒦` of `(f, X)` and `ℒ`
of `(g, Y)` are defined (`TauCeti.IsAdaptedPseudoGradient.signedMorseComplex`), the integral Morse
complex `𝒫` of the product is defined as well.

This file identifies `𝒫` with the tensor product complex `𝒦 ⊗ ℒ`
(`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.signedMorseComplexTensorIso`): in degree `n` it
sends `p ⊗ q`, for critical points with `ind p + ind q = n`, to the critical point `(p, q)`. The
Koszul sign `(-1) ^ ind p` of the differential of the tensor product complex is exactly the sign
of the trajectories of the product moving in the second factor, so, unlike the mod-two comparison
`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.morseComplexTensorIso`, this one has to match signs.
The construction follows that mod-two comparison in
`TauCeti.Geometry.Manifold.Morse.Boundary.Kunneth` (itself after `TauCeti.koszulComplex.tensorIso`):
its degreewise comparison maps and their evaluation on `p ⊗ q` are adapted from there to any
commutative ring, with the matching of the Koszul sign with the parity sign added.

Over a principal ideal ring `R` without zero divisors, for instance `ℤ`, the terms of `ℒ` are free,
so the algebraic Künneth theorem (`HomologicalComplex.homologyKunnethShortComplex_shortExact`)
applies to `𝒦 ⊗ ℒ`.
Transported along this isomorphism, as in the cubical Künneth sequence
`TauCeti.cubicalHomologyKunnethShortComplex_shortExact`, it gives the **Künneth short exact
sequence** of integral Morse homology

`0 ⟶ ⨁_{p + q = m + 1} Hₚ(f) ⊗ H_q(g) ⟶ Hₘ₊₁(f ∘ Prod.fst + g ∘ Prod.snd)`
`  ⟶ ⨁_{p + q = m} Tor₁(Hₚ(f), H_q(g)) ⟶ 0`

(`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.signedMorseHomologyKunnethShortComplex_shortExact`),
whose first map is the homology cross product, and its (non-natural) splitting
(`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.signedMorseHomologyKunnethShortComplexSplitting`).
Over `ℤ` the `Tor₁` terms record the homology of the product created by torsion in the integral
Morse homology of the factors, which the cross product does not reach.

The manifolds are taken in `Type`, so that the chain modules over a ring `R : Type u` lie in the
universe `u` of `R`, where Mathlib's category of `R`-modules is monoidal.

## Main declarations

In the namespace `TauCeti.IsAdaptedPseudoGradient.IsMorseSmale`:

* `signedMorseComplexTensorIso`: the tensor product of the integral Morse chain complexes of `M`
  and `N` is isomorphic to the integral Morse chain complex of `M × N`, with
  `signedMorseComplexTensorIso_hom_f_ιTensorObj_single_tmul_single` computing it on `p ⊗ q`.
* `signedMorseHomologyToTor`: the map `Hₘ₊₁(M × N) ⟶ ⨁_{p + q = m} Tor₁(Hₚ(M), H_q(N))`.
* `signedMorseHomologyKunnethShortComplex`: the Künneth short complex of integral Morse homology.
* `signedMorseHomologyKunnethShortComplex_shortExact`: the Künneth theorem, that it is short exact
  over a principal ideal ring without zero divisors.
* `signedMorseHomologyKunnethShortComplexSplitting`: its splitting.

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

universe u

variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {M N : Type} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M] [TopologicalSpace N] [ChartedSpace E' N]
  [IsManifold 𝓘(ℝ, E') ∞ N] [CompactSpace N] [T2Space N]
  {f : M → ℝ} {g : N → ℝ} {X : (z : M) → TangentSpace 𝓘(ℝ, E) z}
  {Y : (z : N) → TangentSpace 𝓘(ℝ, E') z}
  {hX : IsAdaptedPseudoGradient f X} {hY : IsAdaptedPseudoGradient g Y}
  (hXs : hX.IsMorseSmale) (hYs : hY.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)
  (hg : IsMorse 𝓘(ℝ, E') g) (𝔬 : MorseOrientation f X) (𝔬' : MorseOrientation g Y)
  (R : Type u) [CommRing R]
  (hsqX : hX.signedMorseBoundary 𝔬 hf R ∘ₗ hX.signedMorseBoundary 𝔬 hf R = 0)
  (hsqY : hY.signedMorseBoundary 𝔬' hg R ∘ₗ hY.signedMorseBoundary 𝔬' hg R = 0)

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

/-- The integral Morse complex of `(f, X)`. -/
local notation "𝒦" => signedMorseComplex hX 𝔬 hf R hsqX

/-- The integral Morse complex of `(g, Y)`. -/
local notation "ℒ" => signedMorseComplex hY 𝔬' hg R hsqY

/-- The parity sign `p ↦ (-1) ^ ind p • p` on the Morse chains of `f`. -/
local notation "ε" => LinearEquiv.toLinearMap (Finsupp.signEquiv (A := R) R
  fun p : criticalPoints 𝓘(ℝ, E) f ↦ (-1) ^ manifoldMorseIndex 𝓘(ℝ, E) f p)

/-- The integral Morse complex of the separated sum with the product field and the product
orientation data. -/
local notation "𝒫" =>
  signedMorseComplex (hX.prod hY) (𝔬.prod 𝔬' hX.mdifferentiable hY.mdifferentiable)
    (IsMorse.comp_fst_add_comp_snd_chartedSpaceProd hf hg) R
    (signedMorseBoundary_comp_signedMorseBoundary_prod hf hg 𝔬 𝔬' hXs hYs R hsqX hsqY)

/-- The term of degree `n` of the Morse complex of the separated sum, written without the field. The
comparison maps are stated with this target: it is the term `(𝒫).X n` by definition, but terms
mentioning the product field cannot be rewritten, since its tangent spaces are those of the product
model `𝓘(ℝ, E).prod 𝓘(ℝ, E')`. -/
local notation "𝒞[" n "]" => ModuleCat.of R (ℐ[n] →₀ R)

omit [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [T2Space M] [IsManifold 𝓘(ℝ, E') ∞ N]
  [CompactSpace N] [T2Space N] in
include hf hg in
/-- The Morse index of a critical point `(p, q)` of the separated sum is `ind p + ind q`. -/
private theorem morseIndex_prod (P : criticalPoints 𝓘(ℝ, E × E') (f ∘ Prod.fst + g ∘ Prod.snd)) :
    manifoldMorseIndex 𝓘(ℝ, E × E') (f ∘ Prod.fst + g ∘ Prod.snd) (P : M × N) =
      manifoldMorseIndex 𝓘(ℝ, E) f (P : M × N).1 + manifoldMorseIndex 𝓘(ℝ, E') g (P : M × N).2 :=
  manifoldMorseIndex_comp_fst_add_comp_snd_chartedSpaceProd
    ((hf.contMDiff _).of_le (by norm_num)) ((hg.contMDiff _).of_le (by norm_num))

variable {hXs hYs hf hg 𝔬 𝔬' R hsqX hsqY}

/-! ### The comparison in each degree -/

variable (hf hg) in
/-- The critical point `(p, q)` of the separated sum, of index `n` when `ind p + ind q = n`. -/
private def prodPoint {p q n : ℕ} (h : p + q = n) (a : ℐ₁[p]) (b : ℐ₂[q]) : ℐ[n] :=
  ⟨(eFG).symm (a.val, b.val), by
    rw [morseIndex_prod hf hg, coe_criticalPointsCompFstAddCompSndEquiv_symm, a.property,
      b.property, h]⟩

variable (hf hg R) in
/-- The comparison map on the summand `Cₚ(f) ⊗ C_q(g)`, sending `p ⊗ q` to `(p, q)`. -/
private def toProdLinear (p q n : ℕ) (h : p + q = n) :
    ((ℐ₁[p] →₀ R) ⊗[R] (ℐ₂[q] →₀ R)) →ₗ[R] (ℐ[n] →₀ R) :=
  Finsupp.lmapDomain R R (fun ab ↦ prodPoint (hX := hX) (hY := hY) hf hg h ab.1 ab.2)
    ∘ₗ (finsuppTensorFinsupp' R _ _).toLinearMap

variable (hf hg 𝔬 𝔬' R hsqX hsqY) in
/-- The comparison map from the tensor product of the integral Morse complexes to the integral
Morse complex of the product in degree `n`. -/
private def toProd (n : ℕ) : (𝒦 ⊗ ℒ).X n ⟶ 𝒞[n] :=
  mapBifunctorDesc fun p q h ↦ ModuleCat.ofHom (toProdLinear (hX := hX) (hY := hY) hf hg R p q n h)

private theorem toProd_ιTensorObj_apply (p q n : ℕ) (h : p + q = n)
    (z : (ℐ₁[p] →₀ R) ⊗[R] (ℐ₂[q] →₀ R)) :
    (toProd hf hg 𝔬 𝔬' R hsqX hsqY n).hom ((ιTensorObj 𝒦 ℒ p q n h).hom z) =
      toProdLinear (hX := hX) (hY := hY) hf hg R p q n h z :=
  congr($(ι_mapBifunctorDesc (K₁ := 𝒦) (K₂ := ℒ) (F := curriedTensor (ModuleCat R))
    (c := ComplexShape.down ℕ)
    (fun p q h ↦ ModuleCat.ofHom (toProdLinear (hX := hX) (hY := hY) hf hg R p q n h)) p q h).hom z)

omit [CompactSpace M] [T2Space M] [CompactSpace N] [T2Space N] in
private theorem toProdLinear_single_tmul_single {p q n : ℕ} (h : p + q = n) (a : ℐ₁[p])
    (b : ℐ₂[q]) (r s : R) :
    toProdLinear (hX := hX) (hY := hY) hf hg R p q n h
        (Finsupp.single a r ⊗ₜ Finsupp.single b s) =
      Finsupp.single (prodPoint (hX := hX) (hY := hY) hf hg h a b) (r * s) := by
  simp [toProdLinear, finsuppTensorFinsupp'_single_tmul_single]

variable (hf hg 𝔬 𝔬' R hsqX hsqY) in
/-- The element `p ⊗ q` of the tensor product complex attached to a critical point `(p, q)` of
index `n` of the separated sum. -/
private def prodTensor {n : ℕ} (P : ℐ[n]) : (𝒦 ⊗ ℒ).X n :=
  (ιTensorObj 𝒦 ℒ _ _ n ((morseIndex_prod hf hg P.val).symm.trans P.property)).hom
    (Finsupp.single (⟨(eFG P.val).1, by rw [coe_criticalPointsCompFstAddCompSndEquiv_fst]⟩ :
        ℐ₁[manifoldMorseIndex 𝓘(ℝ, E) f (P.val : M × N).1]) (1 : R) ⊗ₜ
      Finsupp.single (⟨(eFG P.val).2, by rw [coe_criticalPointsCompFstAddCompSndEquiv_snd]⟩ :
        ℐ₂[manifoldMorseIndex 𝓘(ℝ, E') g (P.val : M × N).2]) (1 : R))

variable (hf hg 𝔬 𝔬' R hsqX hsqY) in
/-- The comparison map from the integral Morse complex of the product to the tensor product of the
integral Morse complexes in degree `n`, sending `(p, q)` to `p ⊗ q`. -/
private def fromProd (n : ℕ) : 𝒞[n] ⟶ (𝒦 ⊗ ℒ).X n :=
  ModuleCat.ofHom <| Finsupp.linearCombination R
    (prodTensor hf hg 𝔬 𝔬' R hsqX hsqY (n := n))

private theorem fromProd_single {n : ℕ} (P : ℐ[n]) :
    (fromProd hf hg 𝔬 𝔬' R hsqX hsqY n).hom (Finsupp.single P 1) =
      prodTensor hf hg 𝔬 𝔬' R hsqX hsqY P := by
  -- `fromProd` is `ModuleCat.ofHom` of a linear map whose source is only definitionally the term
  -- of the Morse complex, so `ModuleCat.hom_ofHom` does not rewrite.
  change Finsupp.linearCombination R (prodTensor hf hg 𝔬 𝔬' R hsqX hsqY)
    (Finsupp.single P 1) = _
  rw [Finsupp.linearCombination_single, one_smul]

/-- Morphisms out of a summand `Cₚ(f) ⊗ C_q(g)` of the tensor product complex agree once they agree
on the tensor products `p ⊗ q` of critical points. -/
private theorem summand_hom_ext {p q : ℕ} {Z : ModuleCat.{u} R}
    {φ ψ : (𝒦).X p ⊗ (ℒ).X q ⟶ Z}
    (h : ∀ (a : ℐ₁[p]) (b : ℐ₂[q]),
      φ.hom (Finsupp.single a 1 ⊗ₜ Finsupp.single b 1 : (ℐ₁[p] →₀ R) ⊗[R] (ℐ₂[q] →₀ R)) =
        ψ.hom (Finsupp.single a 1 ⊗ₜ Finsupp.single b 1 : (ℐ₁[p] →₀ R) ⊗[R] (ℐ₂[q] →₀ R))) :
    φ = ψ :=
  ModuleCat.hom_ext <| TensorProduct.ext <| Finsupp.lhom_ext' fun a ↦ LinearMap.ext_ring <|
    Finsupp.lhom_ext' fun b ↦ LinearMap.ext_ring (h a b)

/-- Morphisms out of the tensor product complex in degree `n` agree once they agree on the tensor
products `p ⊗ q` of critical points with `ind p + ind q = n`. -/
private theorem tensor_hom_ext {n : ℕ} {Z : ModuleCat.{u} R} {φ ψ : (𝒦 ⊗ ℒ).X n ⟶ Z}
    (h : ∀ (p q : ℕ) (hpq : p + q = n) (a : ℐ₁[p]) (b : ℐ₂[q]),
      φ.hom ((ιTensorObj 𝒦 ℒ p q n hpq).hom (Finsupp.single a 1 ⊗ₜ Finsupp.single b 1 :
          (ℐ₁[p] →₀ R) ⊗[R] (ℐ₂[q] →₀ R))) =
        ψ.hom ((ιTensorObj 𝒦 ℒ p q n hpq).hom (Finsupp.single a 1 ⊗ₜ Finsupp.single b 1 :
          (ℐ₁[p] →₀ R) ⊗[R] (ℐ₂[q] →₀ R)))) :
    φ = ψ :=
  mapBifunctor.hom_ext fun p q hpq ↦ summand_hom_ext fun a b ↦ h p q hpq a b

/-- The summand inclusions of the tensor product complex agree on `p ⊗ q` whatever the names of
the degrees of `p` and `q`. -/
private theorem ιTensorObj_single_tmul_single_congr {p q p' q' n : ℕ} (hp : p' = p) (hq : q' = q)
    (h : p + q = n) (h' : p' + q' = n) (a : ℐ₁[p]) (a' : ℐ₁[p']) (b : ℐ₂[q]) (b' : ℐ₂[q'])
    (ha : a'.val = a.val) (hb : b'.val = b.val) :
    (ιTensorObj 𝒦 ℒ p' q' n h').hom (Finsupp.single a' (1 : R) ⊗ₜ Finsupp.single b' 1) =
      (ιTensorObj 𝒦 ℒ p q n h).hom (Finsupp.single a (1 : R) ⊗ₜ Finsupp.single b 1) := by
  subst hp hq
  obtain rfl : a' = a := Subtype.ext ha
  obtain rfl : b' = b := Subtype.ext hb
  rfl

variable (hf hg 𝔬 𝔬' R hsqX hsqY) in
/-- The comparison in degree `n` is an isomorphism. -/
private def degreeIso (n : ℕ) : (𝒦 ⊗ ℒ).X n ≅ 𝒞[n] where
  hom := toProd hf hg 𝔬 𝔬' R hsqX hsqY n
  inv := fromProd hf hg 𝔬 𝔬' R hsqX hsqY n
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
    change (toProd hf hg 𝔬 𝔬' R hsqX hsqY n).hom
      ((fromProd hf hg 𝔬 𝔬' R hsqX hsqY n).hom (Finsupp.single P 1)) = Finsupp.single P 1
    rw [fromProd_single]
    refine (toProd_ιTensorObj_apply _ _ _ _ _).trans <|
      (toProdLinear_single_tmul_single _ _ _ _ _).trans ?_
    rw [mul_one]
    exact congrArg (Finsupp.single · 1) (Subtype.ext ((eFG).symm_apply_apply P.val))

/-! ### The comparison commutes with the differentials -/

variable (hX hY R) in
/-- The graded Morse chains of index `n` of the product, included into all Morse chains of the
product and read as the tensor product of the Morse chains of the factors. -/
private def totalChains (n : ℕ) :
    (ℐ[n] →₀ R) →ₗ[R] (criticalPoints 𝓘(ℝ, E) f →₀ R) ⊗[R] (criticalPoints 𝓘(ℝ, E') g →₀ R) :=
  (morseChainProdEquiv f g R hX.mdifferentiable hY.mdifferentiable).toLinearMap ∘ₗ
    Finsupp.lmapDomain R R Subtype.val

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [CompactSpace M] [T2Space M]
  [CompactSpace N] [T2Space N] in
private theorem totalChains_injective (n : ℕ) : Function.Injective (totalChains hX hY R n) :=
  (LinearEquiv.injective _).comp (Finsupp.mapDomain_injective Subtype.val_injective)

omit [CompactSpace M] [T2Space M] [CompactSpace N] [T2Space N] in
private theorem totalChains_toProdLinear (p q n : ℕ) (h : p + q = n)
    (z : (ℐ₁[p] →₀ R) ⊗[R] (ℐ₂[q] →₀ R)) :
    totalChains hX hY R n (toProdLinear (hX := hX) (hY := hY) hf hg R p q n h z) =
      TensorProduct.map (Finsupp.lmapDomain R R Subtype.val)
        (Finsupp.lmapDomain R R Subtype.val) z := by
  have : totalChains hX hY R n ∘ₗ toProdLinear (hX := hX) (hY := hY) hf hg R p q n h =
      TensorProduct.map (Finsupp.lmapDomain R R Subtype.val)
        (Finsupp.lmapDomain R R Subtype.val) := by
    refine TensorProduct.ext <| Finsupp.lhom_ext' fun a ↦ LinearMap.ext_ring <|
      Finsupp.lhom_ext' fun b ↦ LinearMap.ext_ring ?_
    simp only [totalChains, LinearMap.compr₂ₛₗ_apply, TensorProduct.mk_apply, LinearMap.coe_comp,
      LinearEquiv.coe_coe, Function.comp_apply, Finsupp.lsingle_apply,
      toProdLinear_single_tmul_single, mul_one, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
      TensorProduct.map_tmul]
    exact morseChainProdEquiv_single (R := R) a.val b.val 1
  exact LinearMap.congr_fun this z

/-- Read on all Morse chains, the integral Morse boundary of the product is `∂ ⊗ 1 + ε ⊗ ∂`. -/
private theorem totalChains_d (n : ℕ) (w : ℐ[n + 1] →₀ R) :
    totalChains hX hY R n (((𝒫).d (n + 1) n).hom w) =
      ((hX.signedMorseBoundary 𝔬 hf R).rTensor (criticalPoints 𝓘(ℝ, E') g →₀ R) +
          TensorProduct.map ε (hY.signedMorseBoundary 𝔬' hg R))
        (totalChains hX hY R (n + 1) w) := by
  refine (congrArg (totalChains hX hY R n) (signedMorseComplex_d_apply _ n w)).trans ?_
  simp only [totalChains, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    Finsupp.lmapDomain_apply]
  exact (congrArg _ (mapDomain_signedMorseBoundaryAt _ w)).trans
    (LinearMap.congr_fun (hXs.morseChainProdEquiv_comp_signedMorseBoundary hf hg 𝔬 𝔬' hYs R) _)

/-- Read on all Morse chains, the comparison map carries `∂ x ⊗ y` to `∂ x ⊗ y`. -/
private theorem totalChains_toProd_whiskerRight (r q n : ℕ) (h : r + q = n)
    (x : ℐ₁[r + 1] →₀ R) (y : ℐ₂[q] →₀ R) :
    totalChains hX hY R n ((toProd hf hg 𝔬 𝔬' R hsqX hsqY n).hom ((ιTensorObj 𝒦 ℒ r q n h).hom
        (((𝒦).d (r + 1) r ▷ (ℒ).X q).hom
          (x ⊗ₜ y : (ℐ₁[r + 1] →₀ R) ⊗[R] (ℐ₂[q] →₀ R))))) =
      hX.signedMorseBoundary 𝔬 hf R (x.mapDomain Subtype.val) ⊗ₜ y.mapDomain Subtype.val := by
  -- The chains `x` and `y` are elements of the free modules on critical points, which are the terms
  -- of `𝒦` and `ℒ` only by definition. The lemmas used here state chains at one or the other of
  -- these types (`signedMorseComplex_d_apply` at the free module, `whiskerRight_apply` at the term
  -- of the complex), so with either type for `x` some `rw` or `simp only` step fails to match or
  -- produces an ill-typed motive. The steps are therefore chained with `congrArg` and `Eq.trans`,
  -- which compare these types up to unfolding.
  refine (congrArg (fun z ↦ totalChains hX hY R n ((toProd hf hg 𝔬 𝔬' R hsqX hsqY n).hom
    ((ιTensorObj 𝒦 ℒ r q n h).hom z)))
      ((ModuleCat.MonoidalCategory.whiskerRight_apply _ _ _ _).trans
        (congrArg (· ⊗ₜ[R] y) (signedMorseComplex_d_apply hsqX r x)))).trans ?_
  refine (congrArg (totalChains hX hY R n) (toProd_ιTensorObj_apply r q n h _)).trans <|
    (totalChains_toProdLinear r q n h _).trans <| (TensorProduct.map_tmul _ _ _ _).trans ?_
  exact congrArg (· ⊗ₜ[R] _) (mapDomain_signedMorseBoundaryAt hf x)

/-- Read on all Morse chains, the comparison map carries `x ⊗ ∂ y` to `x ⊗ ∂ y`. -/
private theorem totalChains_toProd_whiskerLeft (p s n : ℕ) (h : p + s = n)
    (x : ℐ₁[p] →₀ R) (y : ℐ₂[s + 1] →₀ R) :
    totalChains hX hY R n ((toProd hf hg 𝔬 𝔬' R hsqX hsqY n).hom ((ιTensorObj 𝒦 ℒ p s n h).hom
        (((𝒦).X p ◁ (ℒ).d (s + 1) s).hom
          (x ⊗ₜ y : (ℐ₁[p] →₀ R) ⊗[R] (ℐ₂[s + 1] →₀ R))))) =
      x.mapDomain Subtype.val ⊗ₜ hY.signedMorseBoundary 𝔬' hg R (y.mapDomain Subtype.val) := by
  -- As in `totalChains_toProd_whiskerRight`, the chains live at two definitionally equal types, so
  -- the steps are chained with `congrArg` and `Eq.trans` rather than rewritten.
  refine (congrArg (fun z ↦ totalChains hX hY R n ((toProd hf hg 𝔬 𝔬' R hsqX hsqY n).hom
    ((ιTensorObj 𝒦 ℒ p s n h).hom z)))
      ((ModuleCat.MonoidalCategory.whiskerLeft_apply _ _ _ _).trans
        (congrArg (x ⊗ₜ[R] ·) (signedMorseComplex_d_apply hsqY s y)))).trans ?_
  refine (congrArg (totalChains hX hY R n) (toProd_ιTensorObj_apply p s n h _)).trans <|
    (totalChains_toProdLinear p s n h _).trans <| (TensorProduct.map_tmul _ _ _ _).trans ?_
  exact congrArg (_ ⊗ₜ[R] ·) (mapDomain_signedMorseBoundaryAt hg y)

/-- Read on all Morse chains, the comparison map carries the differential of the tensor product
complex on `p ⊗ q` to `∂ p ⊗ q + (-1) ^ ind p p ⊗ ∂ q`: the Koszul sign of the tensor product
differential is the parity sign `ε`, and a term in which a critical point of index zero is
differentiated vanishes on both sides. -/
private theorem totalChains_toProd_d (p q n : ℕ) (h : p + q = n + 1) (a : ℐ₁[p]) (b : ℐ₂[q]) :
    totalChains hX hY R n ((ιTensorObj 𝒦 ℒ p q (n + 1) h ≫ (𝒦 ⊗ ℒ).d (n + 1) n ≫
        toProd hf hg 𝔬 𝔬' R hsqX hsqY n).hom (Finsupp.single a 1 ⊗ₜ Finsupp.single b 1 :
          (ℐ₁[p] →₀ R) ⊗[R] (ℐ₂[q] →₀ R))) =
      ((hX.signedMorseBoundary 𝔬 hf R).rTensor (criticalPoints 𝓘(ℝ, E') g →₀ R) +
          TensorProduct.map ε (hY.signedMorseBoundary 𝔬' hg R))
        (Finsupp.single a.val 1 ⊗ₜ Finsupp.single b.val 1) := by
  have hd : (𝒦 ⊗ ℒ).d (n + 1) n =
      mapBifunctor.D₁ 𝒦 ℒ (curriedTensor (ModuleCat.{u} R)) (ComplexShape.down ℕ) (n + 1) n +
        mapBifunctor.D₂ 𝒦 ℒ (curriedTensor (ModuleCat.{u} R)) (ComplexShape.down ℕ)
          (n + 1) n :=
    mapBifunctor.d_eq _ _ _ _ _ _
  have hε : ε (Finsupp.single a.val 1) = Finsupp.single a.val ((-1) ^ p) := by
    simp [Finsupp.signEquiv_single, a.property]
  rw [LinearMap.add_apply, LinearMap.rTensor_tmul, TensorProduct.map_tmul, hε, hd,
    Preadditive.add_comp, Preadditive.comp_add]
  rcases p with _ | r <;> rcases q with _ | s
  · omega
  · obtain rfl : s = n := by omega
    rw [ChainComplex.ιTensorObj_D₁_zero_assoc, Limits.zero_comp, zero_add,
      ChainComplex.ιTensorObj_D₂_succ_assoc, pow_zero, one_smul, pow_zero,
      signedMorseBoundary_single_eq_zero_of_morseIndex_eq_zero hf a.property,
      TensorProduct.zero_tmul, zero_add]
    refine (totalChains_toProd_whiskerLeft 0 s s (by omega) _ _).trans ?_
    rw [Finsupp.mapDomain_single, Finsupp.mapDomain_single]
  · obtain rfl : r = n := by omega
    rw [ChainComplex.ιTensorObj_D₂_zero_assoc, Limits.zero_comp, add_zero,
      ChainComplex.ιTensorObj_D₁_succ_assoc,
      signedMorseBoundary_single_eq_zero_of_morseIndex_eq_zero hg b.property,
      TensorProduct.tmul_zero, add_zero]
    refine (totalChains_toProd_whiskerRight r 0 r (by omega) _ _).trans ?_
    rw [Finsupp.mapDomain_single, Finsupp.mapDomain_single]
  · rw [ChainComplex.ιTensorObj_D₁_succ_assoc, ChainComplex.ιTensorObj_D₂_succ_assoc,
      Preadditive.zsmul_comp, ModuleCat.hom_add, ModuleCat.hom_zsmul]
    -- The two terms are rewritten separately by `congrArg₂`: the whiskering lemmas apply to them
    -- only up to unfolding the terms of the Morse complexes
    -- (see `totalChains_toProd_whiskerRight`).
    refine (congrArg (totalChains hX hY R n) (LinearMap.add_apply _ _ _)).trans <|
      (map_add _ _ _).trans <| congrArg₂ (· + ·)
        ((totalChains_toProd_whiskerRight r (s + 1) n (by omega) _ _).trans ?_)
        ((congrArg (totalChains hX hY R n) (LinearMap.smul_apply _ _ _)).trans <|
          (map_zsmul _ _ _).trans <| congrArg (_ • ·)
            (totalChains_toProd_whiskerLeft (r + 1) s n (by omega) _ _) |>.trans ?_)
    · rw [Finsupp.mapDomain_single, Finsupp.mapDomain_single]
    · rw [Finsupp.mapDomain_single, Finsupp.mapDomain_single, TensorProduct.smul_tmul',
        Finsupp.smul_single, zsmul_eq_mul, mul_one, Int.cast_pow, Int.cast_neg, Int.cast_one]

/-- The comparison maps commute with the differentials. -/
private theorem toProd_comm (n : ℕ) :
    toProd hf hg 𝔬 𝔬' R hsqX hsqY (n + 1) ≫ (𝒫).d (n + 1) n =
      (𝒦 ⊗ ℒ).d (n + 1) n ≫ toProd hf hg 𝔬 𝔬' R hsqX hsqY n := by
  refine tensor_hom_ext fun p q h a b ↦ totalChains_injective (hX := hX) (hY := hY) n ?_
  refine (totalChains_d (hXs := hXs) (hYs := hYs) (hf := hf) (hg := hg) (hsqX := hsqX)
    (hsqY := hsqY) n _).trans <|
    Eq.trans ?_ (totalChains_toProd_d p q n h a b).symm
  -- `toProd_ιTensorObj_apply` states the summand at the tensor product of the free modules on
  -- critical points, which is the term of `𝒦 ⊗ ℒ` only by definition, so it is applied under
  -- `congrArg` rather than rewritten (see `totalChains_toProd_whiskerRight`).
  refine (congrArg _ ((congrArg (totalChains hX hY R (n + 1))
    (toProd_ιTensorObj_apply p q (n + 1) h _)).trans <|
      (totalChains_toProdLinear p q (n + 1) h _).trans (TensorProduct.map_tmul _ _ _ _))).trans ?_
  simp only [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

/-! ### The tensor product of the integral Morse complexes -/

variable (hXs hYs hf hg 𝔬 𝔬' R hsqX hsqY) in
/-- **The integral Morse complex of a product is the tensor product of the integral Morse
complexes.** For Morse–Smale pseudo-gradients `X` on `M` and `Y` on `N`, adapted to Morse functions
`f` and `g`, with orientation data `𝔬` and `𝔬'`, and a commutative ring `R` over which both
integral Morse boundaries square to zero, the tensor product of the integral Morse chain complexes
of `(f, X)` and `(g, Y)` is isomorphic to the integral Morse chain complex of the separated sum
`f ∘ Prod.fst + g ∘ Prod.snd` with the product field `(X, Y)` and the product orientation data
`𝔬.prod 𝔬'`. In degree `n` it sends `p ⊗ q`, for critical points `p` and `q` with
`ind p + ind q = n`, to the critical point `(p, q)`
(`signedMorseComplexTensorIso_hom_f_ιTensorObj_single_tmul_single`). -/
def signedMorseComplexTensorIso : 𝒦 ⊗ ℒ ≅ 𝒫 :=
  Hom.isoOfComponents (degreeIso hf hg 𝔬 𝔬' R hsqX hsqY) <| by
    rintro _ n rfl
    exact toProd_comm (hXs := hXs) (hYs := hYs) n

/-- `signedMorseComplexTensorIso` sends `p ⊗ q` to the critical point `(p, q)` of the separated
sum, read among all Morse chains of `M × N`. -/
theorem signedMorseComplexTensorIso_hom_f_ιTensorObj_single_tmul_single {p q n : ℕ}
    (h : p + q = n) (a : ℐ₁[p]) (b : ℐ₂[q]) :
    Finsupp.mapDomain Subtype.val
        ((((signedMorseComplexTensorIso hXs hYs hf hg 𝔬 𝔬' R hsqX hsqY).hom.f n).hom
          ((ιTensorObj 𝒦 ℒ p q n h).hom
            (Finsupp.single a 1 ⊗ₜ Finsupp.single b 1 :
              (ℐ₁[p] →₀ R) ⊗[R] (ℐ₂[q] →₀ R)))) : ℐ[n] →₀ R) =
      Finsupp.single ((eFG).symm (a.val, b.val)) 1 :=
  (congrArg (Finsupp.mapDomain Subtype.val) ((toProd_ιTensorObj_apply p q n h _).trans
    ((toProdLinear_single_tmul_single h a b 1 1).trans (by rw [mul_one])))).trans
    (Finsupp.mapDomain_single ..)

/-! ### The Künneth theorem over a principal ideal ring -/

section Kunneth

variable [NoZeroDivisors R] [IsPrincipalIdealRing R]

variable (hXs hYs hf hg 𝔬 𝔬' R hsqX hsqY) in
/-- The map `Hₘ₊₁(f ∘ Prod.fst + g ∘ Prod.snd) ⟶ ⨁_{p + q = m} Tor₁(Hₚ(f), H_q(g))` of the
Künneth sequence of integral Morse homology: the map induced on homology by the inverse of
`signedMorseComplexTensorIso`, followed by the map to `Tor₁` of the algebraic Künneth sequence
(`HomologicalComplex.homologyToTor`). -/
def signedMorseHomologyToTor (m : ℕ) : (𝒫).homology (m + 1) ⟶ homologyTor 𝒦 ℒ m :=
  homologyMap (signedMorseComplexTensorIso hXs hYs hf hg 𝔬 𝔬' R hsqX hsqY).inv (m + 1) ≫
    homologyToTor 𝒦 ℒ m

/-- The map induced by `signedMorseComplexTensorIso` followed by the map to `Tor₁` of integral
Morse homology is the map to `Tor₁` of the algebraic Künneth sequence. -/
@[reassoc (attr := simp)]
theorem homologyMap_signedMorseComplexTensorIso_hom_comp_signedMorseHomologyToTor (m : ℕ) :
    homologyMap (signedMorseComplexTensorIso hXs hYs hf hg 𝔬 𝔬' R hsqX hsqY).hom (m + 1) ≫
        signedMorseHomologyToTor hXs hYs hf hg 𝔬 𝔬' R hsqX hsqY m =
      homologyToTor 𝒦 ℒ m := by
  rw [signedMorseHomologyToTor, ← Category.assoc, ← homologyMap_comp, Iso.hom_inv_id,
    homologyMap_id, Category.id_comp]

variable (hXs hYs hf hg 𝔬 𝔬' R hsqX hsqY) in
/-- The Künneth short complex of integral Morse homology,
`⨁_{p + q = m + 1} Hₚ(f) ⊗ H_q(g) ⟶ Hₘ₊₁(f ∘ Prod.fst + g ∘ Prod.snd)`
`  ⟶ ⨁_{p + q = m} Tor₁(Hₚ(f), H_q(g))`. Its first map is the homology cross product (the algebraic
Künneth map `HomologicalComplex.homologyKunneth`) followed by the map induced by
`signedMorseComplexTensorIso`, and its second map is `signedMorseHomologyToTor`. -/
abbrev signedMorseHomologyKunnethShortComplex (m : ℕ) : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk
    (homologyKunneth 𝒦 ℒ (m + 1) ≫
      homologyMap (signedMorseComplexTensorIso hXs hYs hf hg 𝔬 𝔬' R hsqX hsqY).hom (m + 1))
    (signedMorseHomologyToTor hXs hYs hf hg 𝔬 𝔬' R hsqX hsqY m) <| by
      rw [Category.assoc,
        homologyMap_signedMorseComplexTensorIso_hom_comp_signedMorseHomologyToTor,
        homologyKunneth_comp_homologyToTor]

variable (hXs hYs hf hg 𝔬 𝔬' R hsqX hsqY) in
/-- The algebraic Künneth short complex of the integral Morse complexes is that of integral Morse
homology, through the isomorphism induced on homology by `signedMorseComplexTensorIso`. -/
private def kunnethShortComplexIso (m : ℕ) :
    homologyKunnethShortComplex 𝒦 ℒ m ≅
      signedMorseHomologyKunnethShortComplex hXs hYs hf hg 𝔬 𝔬' R hsqX hsqY m :=
  ShortComplex.isoMk (Iso.refl _)
    ((homologyFunctor _ _ (m + 1)).mapIso
      (signedMorseComplexTensorIso hXs hYs hf hg 𝔬 𝔬' R hsqX hsqY))
    (Iso.refl _) (Category.id_comp _)
    ((homologyMap_signedMorseComplexTensorIso_hom_comp_signedMorseHomologyToTor m).trans
      (Category.comp_id _).symm)

/-- **The Künneth theorem for integral Morse homology.** For Morse–Smale pseudo-gradients `X` on
`M` and `Y` on `N` with orientation data, over a principal ideal ring `R` without zero divisors,
such as `ℤ`, for which both integral Morse boundaries square to zero, the sequence

`0 ⟶ ⨁_{p + q = m + 1} Hₚ(f) ⊗ H_q(g) ⟶ Hₘ₊₁(f ∘ Prod.fst + g ∘ Prod.snd)`
`  ⟶ ⨁_{p + q = m} Tor₁(Hₚ(f), H_q(g)) ⟶ 0`

of integral Morse homology, with the product field and the product orientation data on `M × N`,
is exact. -/
theorem signedMorseHomologyKunnethShortComplex_shortExact (m : ℕ) :
    (signedMorseHomologyKunnethShortComplex hXs hYs hf hg 𝔬 𝔬' R hsqX hsqY m).ShortExact :=
  ShortComplex.shortExact_of_iso (kunnethShortComplexIso hXs hYs hf hg 𝔬 𝔬' R hsqX hsqY m)
    (homologyKunnethShortComplex_shortExact 𝒦 ℒ m)

variable (hXs hYs hf hg 𝔬 𝔬' R hsqX hsqY) in
/-- **The Künneth sequence of integral Morse homology splits**, so that
`Hₘ₊₁(f ∘ Prod.fst + g ∘ Prod.snd)` is the direct sum of `⨁_{p + q = m + 1} Hₚ(f) ⊗ H_q(g)` and
`⨁_{p + q = m} Tor₁(Hₚ(f), H_q(g))`. The splitting is transported from that of the algebraic
Künneth sequence (`HomologicalComplex.homologyKunnethShortComplexSplitting`), which is built from
chosen splittings of the cycles and is not natural. -/
def signedMorseHomologyKunnethShortComplexSplitting (m : ℕ) :
    (signedMorseHomologyKunnethShortComplex hXs hYs hf hg 𝔬 𝔬' R hsqX hsqY m).Splitting :=
  (homologyKunnethShortComplexSplitting 𝒦 ℒ m).ofIso
    (kunnethShortComplexIso hXs hYs hf hg 𝔬 𝔬' R hsqX hsqY m)

end Kunneth

end IsMorseSmale

end IsAdaptedPseudoGradient

end TauCeti
