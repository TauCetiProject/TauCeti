/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.LocalCoefficient.ExternalTensor
public import TauCeti.Geometry.Manifold.Morse.Boundary.LocalCoefficient
public import TauCeti.Geometry.Manifold.Morse.Boundary.Prod.Integral

/-!
# The Morse boundary of a product with local coefficients

Let `f` be a Morse function on a compact boundaryless manifold `M` with an adapted
pseudo-gradient `X` and orientation data `𝔬`, and likewise `g`, `Y`, `𝔬'` on `N`. For local
coefficient systems `L` on `M` and `K` on `N` of modules over a commutative ring `S`, this file
computes the Morse boundary with coefficients in the external tensor product `L ⊠ K`
(`TauCeti.LocalCoefficientSystem.externalTensor`) of the separated sum `f ∘ Prod.fst + g ∘ Prod.snd`
on `M × N`, for the product field `(X, Y)` and the product orientation data `𝔬.prod 𝔬'`. It is
the tensor product of the twisted boundaries of the factors, with the Koszul sign: the component
from `(p, q)` sends `a ⊗ b`, for `a ∈ L(p)` and `b ∈ K(q)`, to

`∂ a ⊗ b + (-1) ^ ind p • a ⊗ ∂ b`.

This is the analogue with local coefficients of
`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.morseChainProdEquiv_comp_signedMorseBoundary`, the
integral Morse complex of a product.

A trajectory of index one of the product moves only one component
(`TauCeti.IsAdaptedPseudoGradient.morseTrajectorySlice_prod_right`,
`TauCeti.IsAdaptedPseudoGradient.morseTrajectorySlice_prod_left`). The path it traces projects
to the path of the moving component in that factor and to a constant path in the other
(`TauCeti.IsAdaptedPseudoGradient.map_fst_trajectoryPathClass_prod_right` and its three
companions), so transport along it in `L ⊠ K` is transport along the moving component tensored
with the identity (`TauCeti.LocalCoefficientSystem.transport_externalTensor_tmul`). Combined with
the signs of the trajectories of a product
(`TauCeti.IsAdaptedPseudoGradient.trajectorySign_prod_right`,
`TauCeti.IsAdaptedPseudoGradient.trajectorySign_prod_left`), this gives the components of the
boundary:

* `TauCeti.IsAdaptedPseudoGradient.twistedMorseBoundaryMap_prod_right`: from `(p, q)` to
  `(p', q)`, the component of the boundary of `L` from `p` to `p'`, tensored with the identity of
  `K(q)`;
* `TauCeti.IsAdaptedPseudoGradient.twistedMorseBoundaryMap_prod_left`: from `(p, q)` to
  `(p, q')`, `(-1) ^ ind p` times the identity of `L(p)` tensored with the component of the
  boundary of `K` from `q` to `q'`;
* `TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.twistedMorseBoundaryMap_prod_eq_zero_of_ne`:
  between pairs differing in both components, zero.

On chains, the external product `c ⊠ d` of a chain `c` with coefficients in `L` and a chain `d`
with coefficients in `K` (`TauCeti.twistedMorseChainProd`) has boundary `∂ c ⊠ d + ε c ⊠ ∂ d`,
where `ε` multiplies the value at `p` by `(-1) ^ ind p`
(`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.twistedMorseBoundary_twistedMorseChainProd`).
Since the twisted boundary anticommutes with `ε`
(`TauCeti.IsAdaptedPseudoGradient.twistedMorseBoundary_neg_one_pow_smul`), the twisted boundary of
the product squares to zero whenever those of the factors do
(`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.` +
`twistedMorseBoundary_comp_twistedMorseBoundary_prod`).

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §3, Exercise 2 (the Morse complex of a product).
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, §3.H (local coefficients).
-/

public section

open Function Set CategoryTheory
open scoped ContDiff Manifold TensorProduct

universe w v₁ v₂

namespace TauCeti

variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E']
  [NormedSpace ℝ E'] {M : Type v₁} {N : Type v₂} [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace E' N]

attribute [local instance low] chartedSpaceProd

attribute [local instance] isManifold_chartedSpaceProd

/-! ### The external product of chains -/

section Chain

variable {S : Type w} [CommRing S] {f : M → ℝ} {g : N → ℝ}
  (L : LocalCoefficientSystem.{w, v₁, w} S (TopCat.of M))
  (K : LocalCoefficientSystem.{w, v₂, w} S (TopCat.of N))

variable (f g) in
/-- **The external product of chains with local coefficients.** For chains `c` with coefficients
in `L` on the critical points of `f` and `d` with coefficients in `K` on those of `g`, the chain
`c ⊠ d` with coefficients in `L ⊠ K` on the critical points of the separated sum, whose value at
`(p, q)` is `c p ⊗ d q`. -/
noncomputable def twistedMorseChainProd (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f)
    (hg : MDifferentiable 𝓘(ℝ, E') 𝓘(ℝ) g) :
    ((p : criticalPoints 𝓘(ℝ, E) f) → L.obj (FundamentalGroupoid.mk (p : M))) →ₗ[S]
      ((q : criticalPoints 𝓘(ℝ, E') g) → K.obj (FundamentalGroupoid.mk (q : N))) →ₗ[S]
        ((P : criticalPoints 𝓘(ℝ, E × E') (f ∘ Prod.fst + g ∘ Prod.snd)) →
          (L.externalTensor K).obj (FundamentalGroupoid.mk (P : M × N))) :=
  LinearMap.mk₂ S
    (fun c d P ↦ c (criticalPointsCompFstAddCompSndEquiv f g hf hg P).1 ⊗ₜ[S]
      d (criticalPointsCompFstAddCompSndEquiv f g hf hg P).2)
    (fun _ _ _ ↦ funext fun _ ↦ TensorProduct.add_tmul _ _ _)
    (fun _ _ _ ↦ funext fun _ ↦ (TensorProduct.smul_tmul' _ _ _).symm)
    (fun _ _ _ ↦ funext fun _ ↦ TensorProduct.tmul_add _ _ _)
    (fun _ _ _ ↦ funext fun _ ↦ (TensorProduct.tmul_smul _ _ _))

variable {hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f} {hg : MDifferentiable 𝓘(ℝ, E') 𝓘(ℝ) g}

/-- The value of the external product `c ⊠ d` at `(p, q)` is `c p ⊗ d q`. -/
@[simp]
theorem twistedMorseChainProd_apply
    (c : (p : criticalPoints 𝓘(ℝ, E) f) → L.obj (FundamentalGroupoid.mk (p : M)))
    (d : (q : criticalPoints 𝓘(ℝ, E') g) → K.obj (FundamentalGroupoid.mk (q : N)))
    (p : criticalPoints 𝓘(ℝ, E) f) (q : criticalPoints 𝓘(ℝ, E') g) :
    twistedMorseChainProd f g L K hf hg c d ((criticalPointsCompFstAddCompSndEquiv f g hf hg).symm
      (p, q)) = c p ⊗ₜ[S] d q :=
  (rfl)

/-- The external product of chains supported at single critical points `p` and `q` is supported
at `(p, q)`. -/
theorem twistedMorseChainProd_single_single [DecidableEq (criticalPoints 𝓘(ℝ, E) f)]
    [DecidableEq (criticalPoints 𝓘(ℝ, E') g)]
    [DecidableEq (criticalPoints 𝓘(ℝ, E × E') (f ∘ Prod.fst + g ∘ Prod.snd))]
    (p : criticalPoints 𝓘(ℝ, E) f) (q : criticalPoints 𝓘(ℝ, E') g)
    (a : L.obj (FundamentalGroupoid.mk (p : M))) (b : K.obj (FundamentalGroupoid.mk (q : N))) :
    twistedMorseChainProd f g L K hf hg (Pi.single p a) (Pi.single q b) =
      Pi.single ((criticalPointsCompFstAddCompSndEquiv f g hf hg).symm (p, q)) (a ⊗ₜ[S] b) := by
  set e := criticalPointsCompFstAddCompSndEquiv f g hf hg
  -- The fibres of `L ⊠ K` are tensor products of fibres only up to unfolding, so the values of
  -- the single chain of the product are named with their family.
  let F (P : criticalPoints 𝓘(ℝ, E × E') (f ∘ Prod.fst + g ∘ Prod.snd)) : Type w :=
    (L.externalTensor K).obj (FundamentalGroupoid.mk (P : M × N))
  funext P
  obtain ⟨⟨p', q'⟩, rfl⟩ := e.symm.surjective P
  rw [twistedMorseChainProd_apply]
  by_cases hp : p' = p
  · subst hp
    by_cases hq : q' = q
    · subst hq
      rw [Pi.single_eq_same, Pi.single_eq_same]
      exact (Pi.single_eq_same (M := F) (e.symm (p', q')) _).symm
    · rw [Pi.single_eq_of_ne hq, TensorProduct.tmul_zero]
      exact (Pi.single_eq_of_ne (M := F) (i := e.symm (p', q)) (i' := e.symm (p', q'))
        (fun h ↦ hq (congrArg Prod.snd (e.symm.injective h))) _).symm
  · rw [Pi.single_eq_of_ne hp, TensorProduct.zero_tmul]
    exact (Pi.single_eq_of_ne (M := F) (i := e.symm (p, q)) (i' := e.symm (p', q'))
      (fun h ↦ hp (congrArg Prod.fst (e.symm.injective h))) _).symm

end Chain

namespace IsAdaptedPseudoGradient

variable [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, E') ∞ N] [FiniteDimensional ℝ E]
  [FiniteDimensional ℝ E'] [CompactSpace M] [T2Space M] [CompactSpace N] [T2Space N]
  {f : M → ℝ} {g : N → ℝ} {X : (z : M) → TangentSpace 𝓘(ℝ, E) z}
  {Y : (z : N) → TangentSpace 𝓘(ℝ, E') z} (hX : IsAdaptedPseudoGradient f X)
  (hY : IsAdaptedPseudoGradient g Y)

/-! ### Paths along the trajectories of a product -/

/-- Along a trajectory of the product constant in the second factor, the path traced projects to
the path traced in the first factor. -/
theorem map_fst_trajectoryPathClass_prod_right {y : N} {p p' : M}
    (x : hX.morseTrajectorySlice p p')
    (hz : ((x : M), y) ∈ (hX.prod hY).morseTrajectorySlice (p, y) (p', y)) :
    ((hX.prod hY).trajectoryPathClass ⟨_, hz⟩).map ContinuousMap.fst =
      hX.trajectoryPathClass x := by
  -- The product field has its tangent spaces for the model `𝓘(ℝ, E).prod 𝓘(ℝ, E')`, so `rw`
  -- cannot unfold its path classes; `Eq.trans` chains the formulas.
  refine (congrArg (Path.Homotopic.Quotient.map · ContinuousMap.fst)
    ((hX.prod hY).trajectoryPathClass_def _)).trans ?_
  rw [trajectoryPathClass_def, ← Path.Homotopic.Quotient.mk_map]
  exact congrArg _ (Flow.connectingPath_map continuous_fst
    (fun t z ↦ by rw [hX.flow_prod_apply hY]) _ _ _ _)

/-- Along a trajectory of the product constant in the second factor, the path traced projects to
the constant path in the second factor. -/
theorem map_snd_trajectoryPathClass_prod_right {y : N} {p p' : M}
    (z : (hX.prod hY).morseTrajectorySlice (p, y) (p', y)) :
    ((hX.prod hY).trajectoryPathClass z).map ContinuousMap.snd =
      Path.Homotopic.Quotient.refl y := by
  obtain ⟨⟨z₁, z₂⟩, hz⟩ := z
  have hz' := (hX.prod hY).mem_morseTrajectorySlice.1 hz
  rw [hX.unstableSet_prod hY, hX.stableSet_prod hY] at hz'
  obtain ⟨⟨-, hu⟩, ⟨-, hs⟩, -⟩ := hz'
  obtain rfl : z₂ = y := hY.eq_of_mem_unstableSet_inter_stableSet ⟨hu, hs⟩
  refine (congrArg (Path.Homotopic.Quotient.map · ContinuousMap.snd)
    ((hX.prod hY).trajectoryPathClass_def _)).trans ?_
  rw [← Path.Homotopic.Quotient.mk_map, ← Path.Homotopic.Quotient.mk_refl]
  exact congrArg _ ((Flow.connectingPath_map continuous_snd
    (fun t z ↦ by rw [hX.flow_prod_apply hY]) _ _ hu hs).trans
      (Flow.connectingPath_eq_refl (Flow.self_mem_unstableSet_iff.1 hu) hu hs))

/-- Along a trajectory of the product constant in the first factor, the path traced projects to
the path traced in the second factor. -/
theorem map_snd_trajectoryPathClass_prod_left {x : M} {q q' : N}
    (w : hY.morseTrajectorySlice q q')
    (hz : (x, (w : N)) ∈ (hX.prod hY).morseTrajectorySlice (x, q) (x, q')) :
    ((hX.prod hY).trajectoryPathClass ⟨_, hz⟩).map ContinuousMap.snd =
      hY.trajectoryPathClass w := by
  -- The product field has its tangent spaces for the model `𝓘(ℝ, E).prod 𝓘(ℝ, E')`, so `rw`
  -- cannot unfold its path classes; `Eq.trans` chains the formulas.
  refine (congrArg (Path.Homotopic.Quotient.map · ContinuousMap.snd)
    ((hX.prod hY).trajectoryPathClass_def _)).trans ?_
  rw [trajectoryPathClass_def, ← Path.Homotopic.Quotient.mk_map]
  exact congrArg _ (Flow.connectingPath_map continuous_snd
    (fun t z ↦ by rw [hX.flow_prod_apply hY]) _ _ _ _)

/-- Along a trajectory of the product constant in the first factor, the path traced projects to
the constant path in the first factor. -/
theorem map_fst_trajectoryPathClass_prod_left {x : M} {q q' : N}
    (z : (hX.prod hY).morseTrajectorySlice (x, q) (x, q')) :
    ((hX.prod hY).trajectoryPathClass z).map ContinuousMap.fst =
      Path.Homotopic.Quotient.refl x := by
  obtain ⟨⟨z₁, z₂⟩, hz⟩ := z
  have hz' := (hX.prod hY).mem_morseTrajectorySlice.1 hz
  rw [hX.unstableSet_prod hY, hX.stableSet_prod hY] at hz'
  obtain ⟨⟨hu, -⟩, ⟨hs, -⟩, -⟩ := hz'
  obtain rfl : z₁ = x := hX.eq_of_mem_unstableSet_inter_stableSet ⟨hu, hs⟩
  refine (congrArg (Path.Homotopic.Quotient.map · ContinuousMap.fst)
    ((hX.prod hY).trajectoryPathClass_def _)).trans ?_
  rw [← Path.Homotopic.Quotient.mk_map, ← Path.Homotopic.Quotient.mk_refl]
  exact congrArg _ ((Flow.connectingPath_map continuous_fst
    (fun t z ↦ by rw [hX.flow_prod_apply hY]) _ _ hu hs).trans
      (Flow.connectingPath_eq_refl (Flow.self_mem_unstableSet_iff.1 hu) hu hs))

/-! ### The components of the twisted boundary of a product -/

variable {S : Type w} [CommRing S] (hf : IsMorse 𝓘(ℝ, E) f) (hg : IsMorse 𝓘(ℝ, E') g)
  (𝔬 : MorseOrientation f X) (𝔬' : MorseOrientation g Y)
  (L : LocalCoefficientSystem.{w, v₁, w} S (TopCat.of M))
  (K : LocalCoefficientSystem.{w, v₂, w} S (TopCat.of N))

omit [CompactSpace M] [T2Space M] [CompactSpace N] [T2Space N] in
include hf hg in
/-- The Morse index of the separated sum at `(p, q)` is `ind p + ind q`, for Morse `f` and `g`. -/
private theorem manifoldMorseIndex_symm_pair (p : criticalPoints 𝓘(ℝ, E) f)
    (q : criticalPoints 𝓘(ℝ, E') g) :
    manifoldMorseIndex 𝓘(ℝ, E × E') (f ∘ Prod.fst + g ∘ Prod.snd)
        ((criticalPointsCompFstAddCompSndEquiv f g hX.mdifferentiable hY.mdifferentiable).symm
          (p, q) : M × N) =
      manifoldMorseIndex 𝓘(ℝ, E) f p + manifoldMorseIndex 𝓘(ℝ, E') g q :=
  manifoldMorseIndex_criticalPointsCompFstAddCompSndEquiv_symm
    (hf.contMDiff.of_le (by norm_num)) (hg.contMDiff.of_le (by norm_num)) p q

/-- Transport in `L ⊠ K` along a trajectory of the product constant in the second factor is
transport in `L` along the trajectory of the first factor, tensored with the identity. -/
private theorem transport_externalTensor_trajectoryPathClass_prod_right {y : N}
    {p p' : M} (x : hX.morseTrajectorySlice p p')
    (hz : ((x : M), y) ∈ (hX.prod hY).morseTrajectorySlice (p, y) (p', y))
    (a : L.obj (FundamentalGroupoid.mk p)) (b : K.obj (FundamentalGroupoid.mk y)) :
    LocalCoefficientSystem.transport (L.externalTensor K)
        ((hX.prod hY).trajectoryPathClass ⟨_, hz⟩) (a ⊗ₜ[S] b) =
      LocalCoefficientSystem.transport L (hX.trajectoryPathClass x) a ⊗ₜ[S] b :=
  (LocalCoefficientSystem.transport_externalTensor_tmul L K
    ((hX.prod hY).trajectoryPathClass ⟨_, hz⟩) a b).trans <|
    congrArg₂ (· ⊗ₜ[S] ·)
      (congrArg (LocalCoefficientSystem.transport L · a)
        (hX.map_fst_trajectoryPathClass_prod_right hY x hz))
      ((congrArg (LocalCoefficientSystem.transport K · b)
        (hX.map_snd_trajectoryPathClass_prod_right hY ⟨_, hz⟩)).trans
          (LinearEquiv.congr_fun (LocalCoefficientSystem.transport_refl K y) b))

/-- Transport in `L ⊠ K` along a trajectory of the product constant in the first factor is the
identity tensored with transport in `K` along the trajectory of the second factor. -/
private theorem transport_externalTensor_trajectoryPathClass_prod_left {x : M} {q q' : N}
    (w : hY.morseTrajectorySlice q q')
    (hz : (x, (w : N)) ∈ (hX.prod hY).morseTrajectorySlice (x, q) (x, q'))
    (a : L.obj (FundamentalGroupoid.mk x)) (b : K.obj (FundamentalGroupoid.mk q)) :
    LocalCoefficientSystem.transport (L.externalTensor K)
        ((hX.prod hY).trajectoryPathClass ⟨_, hz⟩) (a ⊗ₜ[S] b) =
      a ⊗ₜ[S] LocalCoefficientSystem.transport K (hY.trajectoryPathClass w) b :=
  (LocalCoefficientSystem.transport_externalTensor_tmul L K
    ((hX.prod hY).trajectoryPathClass ⟨_, hz⟩) a b).trans <|
    congrArg₂ (· ⊗ₜ[S] ·)
      ((congrArg (LocalCoefficientSystem.transport L · a)
        (hX.map_fst_trajectoryPathClass_prod_left hY ⟨_, hz⟩)).trans
          (LinearEquiv.congr_fun (LocalCoefficientSystem.transport_refl L x) a))
      (congrArg (LocalCoefficientSystem.transport K · b)
        (hX.map_snd_trajectoryPathClass_prod_left hY w hz))

include hf hg in
/-- **The components of the twisted boundary of a product along the first factor.** With
coefficients in `L ⊠ K`, the component of the Morse boundary of the product from `(p, q)` to
`(p', q)` sends `a ⊗ b` to `∂ a ⊗ b`, where `∂ a` is the component of the boundary of `L` from `p`
to `p'`. -/
theorem twistedMorseBoundaryMap_prod_right (hXs : hX.IsMorseSmale)
    (p p' : criticalPoints 𝓘(ℝ, E) f) (q : criticalPoints 𝓘(ℝ, E') g)
    (a : L.obj (FundamentalGroupoid.mk (p : M))) (b : K.obj (FundamentalGroupoid.mk (q : N))) :
    (hX.prod hY).twistedMorseBoundaryMap (𝔬.prod 𝔬' hX.mdifferentiable hY.mdifferentiable)
        (L.externalTensor K)
        ((criticalPointsCompFstAddCompSndEquiv f g hX.mdifferentiable hY.mdifferentiable).symm
          (p, q))
        ((criticalPointsCompFstAddCompSndEquiv f g hX.mdifferentiable hY.mdifferentiable).symm
          (p', q)) (a ⊗ₜ[S] b) =
      hX.twistedMorseBoundaryMap 𝔬 L p p' a ⊗ₜ[S] b := by
  set e := criticalPointsCompFstAddCompSndEquiv f g hX.mdifferentiable hY.mdifferentiable
  have hindP := manifoldMorseIndex_symm_pair hX hY hf hg p q
  have hindQ := manifoldMorseIndex_symm_pair hX hY hf hg p' q
  by_cases hpp' : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f p' + 1
  swap
  · rw [twistedMorseBoundaryMap_of_not_morseIndex_eq_add_one hpp', LinearMap.zero_apply,
      TensorProduct.zero_tmul]
    exact LinearMap.congr_fun (twistedMorseBoundaryMap_of_not_morseIndex_eq_add_one
      (hX := hX.prod hY) (by rw [hindP, hindQ]; omega)) _
  have hPQ :
      manifoldMorseIndex 𝓘(ℝ, E × E') (f ∘ Prod.fst + g ∘ Prod.snd) (e.symm (p, q) : M × N) =
        manifoldMorseIndex 𝓘(ℝ, E × E') (f ∘ Prod.fst + g ∘ Prod.snd) (e.symm (p', q) : M × N) +
          1 := by
    rw [hindP, hindQ, hpp']
    ring
  -- The trajectories of the product from `(p, q)` to `(p', q)` are those of `X` from `p` to `p'`.
  let φ : hX.morseTrajectorySlice p p' ≃
      (hX.prod hY).morseTrajectorySlice (e.symm (p, q) : M × N) (e.symm (p', q) : M × N) :=
    (Equiv.Set.image _ _ (Prod.mk_left_injective _)).trans
      (Set.equivOfEq (hX.morseTrajectorySlice_prod_right hY q.property p p').symm)
  have := (hXs.finite_morseTrajectorySlice hf hpp').to_subtype
  have := Fintype.ofFinite (hX.morseTrajectorySlice p p')
  have hR : hX.twistedMorseBoundaryMap 𝔬 L p p' a ⊗ₜ[S] b = ∑ x : hX.morseTrajectorySlice p p',
      (hX.trajectorySign (𝔬.chart p) (𝔬.chart p') (𝔬.orientation p) (𝔬.orientation p') hpp' x •
        LocalCoefficientSystem.transport L (hX.trajectoryPathClass x) a) ⊗ₜ[S] b := by
    rw [twistedMorseBoundaryMap_of_morseIndex_eq_add_one hpp', finsum_eq_sum_of_fintype,
      LinearMap.sum_apply, TensorProduct.sum_tmul]
    rfl
  refine Eq.trans ?_ hR.symm
  -- The terms of the product cannot be rewritten (see above), so the sum over its trajectories
  -- is reindexed by those of `X` with `Eq.trans`.
  refine (LinearMap.congr_fun (twistedMorseBoundaryMap_of_morseIndex_eq_add_one
    (hX := hX.prod hY) (𝔬 := 𝔬.prod 𝔬' hX.mdifferentiable hY.mdifferentiable)
    (L := L.externalTensor K) hPQ) _).trans ?_
  refine (LinearMap.congr_fun (finsum_comp_equiv φ).symm _).trans ?_
  refine (LinearMap.congr_fun (finsum_eq_sum_of_fintype _) _).trans ?_
  refine (LinearMap.sum_apply _ _ _).trans (Finset.sum_congr rfl fun x _ ↦ ?_)
  obtain ⟨hu, hs, -⟩ := hX.mem_morseTrajectorySlice.1 x.property
  refine (LinearMap.smul_apply _ _ _).trans ?_
  refine (congrArg₂ (· • ·) (trajectorySign_prod_right (hX := hX) (hY := hY)
    (𝔬.coord_mfderiv_chart p) (𝔬.coord_mfderiv_chart p') (𝔬'.coord_mfderiv_chart q) hf hg
    q.property ⟨hu, hs⟩ (bijective_trajectoryComparison (𝔬.coord_mfderiv_chart p)
      (𝔬.coord_mfderiv_chart p') hXs hf hpp' ⟨hu, hs⟩) hpp' hPQ)
    (transport_externalTensor_trajectoryPathClass_prod_right hX hY L K x (φ x).property a b)).trans
      ?_
  exact (TensorProduct.smul_tmul' _ _ _).symm

include hf hg in
/-- **The components of the twisted boundary of a product along the second factor.** With
coefficients in `L ⊠ K`, the component of the Morse boundary of the product from `(p, q)` to
`(p, q')` sends `a ⊗ b` to `(-1) ^ ind p • a ⊗ ∂ b`, where `∂ b` is the component of the boundary
of `K` from `q` to `q'`: the direction of the flow passes the `ind p` directions of the unstable
manifold of `p` in the product orientation. -/
theorem twistedMorseBoundaryMap_prod_left (hYs : hY.IsMorseSmale)
    (p : criticalPoints 𝓘(ℝ, E) f) (q q' : criticalPoints 𝓘(ℝ, E') g)
    (a : L.obj (FundamentalGroupoid.mk (p : M))) (b : K.obj (FundamentalGroupoid.mk (q : N))) :
    (hX.prod hY).twistedMorseBoundaryMap (𝔬.prod 𝔬' hX.mdifferentiable hY.mdifferentiable)
        (L.externalTensor K)
        ((criticalPointsCompFstAddCompSndEquiv f g hX.mdifferentiable hY.mdifferentiable).symm
          (p, q))
        ((criticalPointsCompFstAddCompSndEquiv f g hX.mdifferentiable hY.mdifferentiable).symm
          (p, q')) (a ⊗ₜ[S] b) =
      (-1 : ℤ) ^ manifoldMorseIndex 𝓘(ℝ, E) f p •
        a ⊗ₜ[S] hY.twistedMorseBoundaryMap 𝔬' K q q' b := by
  set e := criticalPointsCompFstAddCompSndEquiv f g hX.mdifferentiable hY.mdifferentiable
  have hindP := manifoldMorseIndex_symm_pair hX hY hf hg p q
  have hindQ := manifoldMorseIndex_symm_pair hX hY hf hg p q'
  by_cases hqq' : manifoldMorseIndex 𝓘(ℝ, E') g q = manifoldMorseIndex 𝓘(ℝ, E') g q' + 1
  swap
  · rw [twistedMorseBoundaryMap_of_not_morseIndex_eq_add_one hqq', LinearMap.zero_apply,
      TensorProduct.tmul_zero, smul_zero]
    exact LinearMap.congr_fun (twistedMorseBoundaryMap_of_not_morseIndex_eq_add_one
      (hX := hX.prod hY) (by rw [hindP, hindQ]; omega)) _
  have hPQ :
      manifoldMorseIndex 𝓘(ℝ, E × E') (f ∘ Prod.fst + g ∘ Prod.snd) (e.symm (p, q) : M × N) =
        manifoldMorseIndex 𝓘(ℝ, E × E') (f ∘ Prod.fst + g ∘ Prod.snd) (e.symm (p, q') : M × N) +
          1 := by
    rw [hindP, hindQ, hqq', add_assoc]
  -- The trajectories of the product from `(p, q)` to `(p, q')` are those of `Y` from `q` to `q'`.
  let φ : hY.morseTrajectorySlice q q' ≃
      (hX.prod hY).morseTrajectorySlice (e.symm (p, q) : M × N) (e.symm (p, q') : M × N) :=
    (Equiv.Set.image _ _ (Prod.mk_right_injective _)).trans
      (Set.equivOfEq (hX.morseTrajectorySlice_prod_left hY p.property q q').symm)
  have := (hYs.finite_morseTrajectorySlice hg hqq').to_subtype
  have := Fintype.ofFinite (hY.morseTrajectorySlice q q')
  have hR : (-1 : ℤ) ^ manifoldMorseIndex 𝓘(ℝ, E) f p •
      a ⊗ₜ[S] hY.twistedMorseBoundaryMap 𝔬' K q q' b = ∑ w : hY.morseTrajectorySlice q q',
        ((-1) ^ manifoldMorseIndex 𝓘(ℝ, E) f p *
          hY.trajectorySign (𝔬'.chart q) (𝔬'.chart q') (𝔬'.orientation q) (𝔬'.orientation q')
            hqq' w) • a ⊗ₜ[S] LocalCoefficientSystem.transport K (hY.trajectoryPathClass w) b := by
    rw [twistedMorseBoundaryMap_of_morseIndex_eq_add_one hqq', finsum_eq_sum_of_fintype,
      LinearMap.sum_apply, TensorProduct.tmul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun w _ ↦ ?_
    rw [LinearMap.smul_apply, TensorProduct.tmul_smul, smul_smul]
    rfl
  refine Eq.trans ?_ hR.symm
  -- As in `twistedMorseBoundaryMap_prod_right`, the sum over the trajectories of the product is
  -- reindexed by those of `Y` with `Eq.trans`.
  refine (LinearMap.congr_fun (twistedMorseBoundaryMap_of_morseIndex_eq_add_one
    (hX := hX.prod hY) (𝔬 := 𝔬.prod 𝔬' hX.mdifferentiable hY.mdifferentiable)
    (L := L.externalTensor K) hPQ) _).trans ?_
  refine (LinearMap.congr_fun (finsum_comp_equiv φ).symm _).trans ?_
  refine (LinearMap.congr_fun (finsum_eq_sum_of_fintype _) _).trans ?_
  refine (LinearMap.sum_apply _ _ _).trans (Finset.sum_congr rfl fun w _ ↦ ?_)
  obtain ⟨hu, hs, -⟩ := hY.mem_morseTrajectorySlice.1 w.property
  refine (LinearMap.smul_apply _ _ _).trans ?_
  exact congrArg₂ (· • ·) (trajectorySign_prod_left (hX := hX) (hY := hY)
    (𝔬.coord_mfderiv_chart p) (𝔬'.coord_mfderiv_chart q) (𝔬'.coord_mfderiv_chart q') hf hg
    p.property ⟨hu, hs⟩ (bijective_trajectoryComparison (𝔬'.coord_mfderiv_chart q)
      (𝔬'.coord_mfderiv_chart q') hYs hg hqq' ⟨hu, hs⟩) hqq' hPQ)
    (transport_externalTensor_trajectoryPathClass_prod_left hX hY L K w (φ w).property a b)

namespace IsMorseSmale

variable {hX hY}

include hf hg in
/-- **No component of the twisted boundary of a product moves both factors.** For Morse–Smale
`X` and `Y`, with coefficients in `L ⊠ K`, the component of the Morse boundary of the product from
`(p, q)` to `(p', q')` vanishes when `p ≠ p'` and `q ≠ q'`. -/
theorem twistedMorseBoundaryMap_prod_eq_zero_of_ne (hXs : hX.IsMorseSmale)
    (hYs : hY.IsMorseSmale) {p p' : criticalPoints 𝓘(ℝ, E) f}
    {q q' : criticalPoints 𝓘(ℝ, E') g} (hpp : p ≠ p') (hqq : q ≠ q') :
    (hX.prod hY).twistedMorseBoundaryMap (𝔬.prod 𝔬' hX.mdifferentiable hY.mdifferentiable)
        (L.externalTensor K)
        ((criticalPointsCompFstAddCompSndEquiv f g hX.mdifferentiable hY.mdifferentiable).symm
          (p, q))
        ((criticalPointsCompFstAddCompSndEquiv f g hX.mdifferentiable hY.mdifferentiable).symm
          (p', q')) = 0 := by
  have hindP := manifoldMorseIndex_symm_pair hX hY hf hg p q
  have hindQ := manifoldMorseIndex_symm_pair hX hY hf hg p' q'
  by_cases hind : manifoldMorseIndex 𝓘(ℝ, E) f p + manifoldMorseIndex 𝓘(ℝ, E') g q =
    manifoldMorseIndex 𝓘(ℝ, E) f p' + manifoldMorseIndex 𝓘(ℝ, E') g q' + 1
  · -- There are no trajectories of the product between these pairs.
    have hempty := hXs.morseTrajectorySlice_prod_eq_empty hYs hf hg
      (fun h ↦ hpp (Subtype.ext h)) (fun h ↦ hqq (Subtype.ext h)) hind.le
    refine (twistedMorseBoundaryMap_of_morseIndex_eq_add_one (hX := hX.prod hY)
      (hindP.trans <| hind.trans <| congrArg (· + 1) hindQ.symm)).trans ?_
    have : IsEmpty ((hX.prod hY).morseTrajectorySlice ((p : M), (q : N)) ((p' : M), (q' : N))) :=
      Set.isEmpty_coe_sort.2 hempty
    exact finsum_of_isEmpty
      (α := (hX.prod hY).morseTrajectorySlice ((p : M), (q : N)) ((p' : M), (q' : N))) _
  · exact twistedMorseBoundaryMap_of_not_morseIndex_eq_add_one (hX := hX.prod hY)
      (by rw [hindP, hindQ]; exact hind)

end IsMorseSmale

include hf hg in
/-- The twisted boundary of the product of single chains, at `(p, q)`. -/
private theorem twistedMorseBoundary_twistedMorseChainProd_single_single (hXs : hX.IsMorseSmale)
    (hYs : hY.IsMorseSmale) [DecidableEq (criticalPoints 𝓘(ℝ, E) f)]
    [DecidableEq (criticalPoints 𝓘(ℝ, E') g)] (p' : criticalPoints 𝓘(ℝ, E) f)
    (q' : criticalPoints 𝓘(ℝ, E') g)
    (a : L.obj (FundamentalGroupoid.mk (p' : M))) (b : K.obj (FundamentalGroupoid.mk (q' : N)))
    (p : criticalPoints 𝓘(ℝ, E) f) (q : criticalPoints 𝓘(ℝ, E') g) :
    (hX.prod hY).twistedMorseBoundary (𝔬.prod 𝔬' hX.mdifferentiable hY.mdifferentiable)
        (L.externalTensor K) (hf.comp_fst_add_comp_snd_chartedSpaceProd hg)
        (twistedMorseChainProd f g L K hX.mdifferentiable hY.mdifferentiable (Pi.single p' a)
          (Pi.single q' b))
        ((criticalPointsCompFstAddCompSndEquiv f g hX.mdifferentiable hY.mdifferentiable).symm
          (p, q)) =
      hX.twistedMorseBoundary 𝔬 L hf (Pi.single p' a) p ⊗ₜ[S]
          Pi.single
            (M := fun r : criticalPoints 𝓘(ℝ, E') g ↦ K.obj (FundamentalGroupoid.mk (r : N)))
            q' b q +
        ((-1 : ℤ) ^ manifoldMorseIndex 𝓘(ℝ, E) f p •
          Pi.single
            (M := fun r : criticalPoints 𝓘(ℝ, E) f ↦ L.obj (FundamentalGroupoid.mk (r : M)))
            p' a p) ⊗ₜ[S]
          hY.twistedMorseBoundary 𝔬' K hg (Pi.single q' b) q := by
  classical
  rw [twistedMorseBoundary_single_apply, twistedMorseBoundary_single_apply,
    twistedMorseChainProd_single_single]
  -- As for the components, the boundary of the product is unfolded with `Eq.trans`.
  refine (twistedMorseBoundary_single_apply (hX := hX.prod hY)
    (𝔬 := 𝔬.prod 𝔬' hX.mdifferentiable hY.mdifferentiable) (L := L.externalTensor K)
    (hf.comp_fst_add_comp_snd_chartedSpaceProd hg) _ _ _).trans ?_
  by_cases hp : p' = p
  · subst hp
    rw [Pi.single_eq_same]
    by_cases hq : q' = q
    · subst hq
      rw [Pi.single_eq_same, twistedMorseBoundaryMap_of_not_morseIndex_eq_add_one (by omega),
        twistedMorseBoundaryMap_of_not_morseIndex_eq_add_one (by omega), LinearMap.zero_apply,
        LinearMap.zero_apply, TensorProduct.zero_tmul, TensorProduct.tmul_zero, add_zero]
      exact LinearMap.congr_fun (twistedMorseBoundaryMap_of_not_morseIndex_eq_add_one
        (hX := hX.prod hY) (by omega)) _
    · rw [Pi.single_eq_of_ne' hq, TensorProduct.tmul_zero, zero_add]
      exact (twistedMorseBoundaryMap_prod_left hX hY hf hg 𝔬 𝔬' L K hYs p' q' q a b).trans
        (TensorProduct.smul_tmul' _ _ _)
  · rw [Pi.single_eq_of_ne' hp, smul_zero, TensorProduct.zero_tmul, add_zero]
    by_cases hq : q' = q
    · subst hq
      rw [Pi.single_eq_same]
      exact twistedMorseBoundaryMap_prod_right hX hY hf hg 𝔬 𝔬' L K hXs p' p q' a b
    · rw [Pi.single_eq_of_ne' hq, TensorProduct.tmul_zero]
      exact (LinearMap.congr_fun (hXs.twistedMorseBoundaryMap_prod_eq_zero_of_ne hf hg 𝔬 𝔬' L K
        hYs hp hq) _).trans (LinearMap.zero_apply _)

namespace IsMorseSmale

variable {hX hY}

include hf hg in
/-- **The twisted Morse boundary of a product is the tensor product boundary.** For Morse–Smale
pseudo-gradients `X` and `Y`, the product orientation data and coefficients in `L ⊠ K`, the
boundary of the external product `c ⊠ d` of chains is `∂ c ⊠ d + ε c ⊠ ∂ d`, where `ε c` multiplies
the value of `c` at each critical point `p` by the Koszul sign `(-1) ^ ind p`. -/
theorem twistedMorseBoundary_twistedMorseChainProd (hXs : hX.IsMorseSmale)
    (hYs : hY.IsMorseSmale)
    (c : (p : criticalPoints 𝓘(ℝ, E) f) → L.obj (FundamentalGroupoid.mk (p : M)))
    (d : (q : criticalPoints 𝓘(ℝ, E') g) → K.obj (FundamentalGroupoid.mk (q : N))) :
    (hX.prod hY).twistedMorseBoundary (𝔬.prod 𝔬' hX.mdifferentiable hY.mdifferentiable)
        (L.externalTensor K) (hf.comp_fst_add_comp_snd_chartedSpaceProd hg)
        (twistedMorseChainProd f g L K hX.mdifferentiable hY.mdifferentiable c d) =
      twistedMorseChainProd f g L K hX.mdifferentiable hY.mdifferentiable
          (hX.twistedMorseBoundary 𝔬 L hf c) d +
        twistedMorseChainProd f g L K hX.mdifferentiable hY.mdifferentiable
          (fun p ↦ (-1 : ℤ) ^ manifoldMorseIndex 𝓘(ℝ, E) f p • c p)
          (hY.twistedMorseBoundary 𝔬' K hg d) := by
  classical
  have := hf.finite_criticalPoints.to_subtype
  have := hg.finite_criticalPoints.to_subtype
  set B := twistedMorseChainProd f g L K hX.mdifferentiable hY.mdifferentiable
  -- The parity sign `ε`, as a linear map on chains.
  let ε : ((p : criticalPoints 𝓘(ℝ, E) f) → L.obj (FundamentalGroupoid.mk (p : M))) →ₗ[S]
      ((p : criticalPoints 𝓘(ℝ, E) f) → L.obj (FundamentalGroupoid.mk (p : M))) :=
    LinearMap.pi fun p ↦ (-1 : ℤ) ^ manifoldMorseIndex 𝓘(ℝ, E) f p • LinearMap.proj p
  -- Both sides are bilinear in `(c, d)`, so it suffices to compare them on single chains.
  have h : B.compr₂ ((hX.prod hY).twistedMorseBoundary
      (𝔬.prod 𝔬' hX.mdifferentiable hY.mdifferentiable) (L.externalTensor K)
        (hf.comp_fst_add_comp_snd_chartedSpaceProd hg)) =
      B ∘ₗ hX.twistedMorseBoundary 𝔬 L hf + (B ∘ₗ ε).compl₂ (hY.twistedMorseBoundary 𝔬' K hg) := by
    refine LinearMap.pi_ext fun p' a ↦ LinearMap.pi_ext fun q' b ↦ funext fun P ↦ ?_
    obtain ⟨⟨p, q⟩, rfl⟩ := (criticalPointsCompFstAddCompSndEquiv f g hX.mdifferentiable
      hY.mdifferentiable).symm.surjective P
    refine (twistedMorseBoundary_twistedMorseChainProd_single_single hX hY hf hg 𝔬 𝔬' L K hXs hYs
      p' q' a b p q).trans ?_
    simp only [B, ε, LinearMap.add_apply, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.compl₂_apply, Pi.add_apply, twistedMorseChainProd_apply, LinearMap.pi_apply,
      LinearMap.smul_apply, LinearMap.coe_proj, Function.eval, twistedMorseBoundary_single_apply]
    -- The two sides now differ only in how the additive structure of the fibre of `L ⊠ K` at
    -- `(p, q)` is presented: as a tensor product of modules, or as an object of `ModuleCat`.
    rfl
  exact LinearMap.congr_fun (LinearMap.congr_fun h c) d

include hf hg in
/-- **The twisted Morse boundary of a product squares to zero when those of the factors do.** For
Morse–Smale pseudo-gradients `X` and `Y`, the product orientation data and coefficients in
`L ⊠ K`, if the twisted boundaries of `(f, X)` with coefficients in `L` and of `(g, Y)` with
coefficients in `K` square to zero, so does that of the separated sum. In the square of
`∂ ⊠ 1 + ε ⊠ ∂` the mixed terms cancel, because the twisted boundary anticommutes with the parity
sign `ε` (`TauCeti.IsAdaptedPseudoGradient.twistedMorseBoundary_neg_one_pow_smul`). -/
theorem twistedMorseBoundary_comp_twistedMorseBoundary_prod (hXs : hX.IsMorseSmale)
    (hYs : hY.IsMorseSmale)
    (hL : hX.twistedMorseBoundary 𝔬 L hf ∘ₗ hX.twistedMorseBoundary 𝔬 L hf = 0)
    (hK : hY.twistedMorseBoundary 𝔬' K hg ∘ₗ hY.twistedMorseBoundary 𝔬' K hg = 0) :
    (hX.prod hY).twistedMorseBoundary (𝔬.prod 𝔬' hX.mdifferentiable hY.mdifferentiable)
        (L.externalTensor K) (hf.comp_fst_add_comp_snd_chartedSpaceProd hg) ∘ₗ
      (hX.prod hY).twistedMorseBoundary (𝔬.prod 𝔬' hX.mdifferentiable hY.mdifferentiable)
        (L.externalTensor K) (hf.comp_fst_add_comp_snd_chartedSpaceProd hg) = 0 := by
  classical
  have := (hf.comp_fst_add_comp_snd_chartedSpaceProd hg).finite_criticalPoints.to_subtype
  set D := (hX.prod hY).twistedMorseBoundary (𝔬.prod 𝔬' hX.mdifferentiable hY.mdifferentiable)
    (L.externalTensor K) (hf.comp_fst_add_comp_snd_chartedSpaceProd hg)
  set B := twistedMorseChainProd f g L K hX.mdifferentiable hY.mdifferentiable
  set dL := hX.twistedMorseBoundary 𝔬 L hf
  set dK := hY.twistedMorseBoundary 𝔬' K hg
  -- The square of the boundary vanishes on external products of chains.
  have hB (c : (p : criticalPoints 𝓘(ℝ, E) f) → L.obj (FundamentalGroupoid.mk (p : M)))
      (d : (q : criticalPoints 𝓘(ℝ, E') g) → K.obj (FundamentalGroupoid.mk (q : N))) :
      D (D (B c d)) = 0 := by
    have hε : (fun r : criticalPoints 𝓘(ℝ, E) f ↦ (-1 : ℤ) ^ manifoldMorseIndex 𝓘(ℝ, E) f r •
        dL c r) + dL (fun r ↦ (-1 : ℤ) ^ manifoldMorseIndex 𝓘(ℝ, E) f r • c r) = 0 :=
      funext fun r ↦ by
      rw [Pi.add_apply, twistedMorseBoundary_neg_one_pow_smul, add_neg_cancel, Pi.zero_apply]
    rw [hXs.twistedMorseBoundary_twistedMorseChainProd hf hg 𝔬 𝔬' L K hYs, map_add,
      hXs.twistedMorseBoundary_twistedMorseChainProd hf hg 𝔬 𝔬' L K hYs,
      hXs.twistedMorseBoundary_twistedMorseChainProd hf hg 𝔬 𝔬' L K hYs,
      show dL (dL c) = 0 from LinearMap.congr_fun hL c,
      show dK (dK d) = 0 from LinearMap.congr_fun hK d, map_zero, LinearMap.zero_apply, map_zero,
      zero_add, add_zero, ← LinearMap.add_apply, ← map_add, hε, map_zero, LinearMap.zero_apply]
  -- The chains of the product are spanned by external products of single chains.
  refine LinearMap.pi_ext fun P x ↦ ?_
  obtain ⟨⟨p, q⟩, rfl⟩ := (criticalPointsCompFstAddCompSndEquiv f g hX.mdifferentiable
    hY.mdifferentiable).symm.surjective P
  induction x using TensorProduct.inductionOn with
  | tmul a b =>
    -- The fibres of `L ⊠ K` are tensor products only up to unfolding, so the single chain is
    -- compared with an external product by `Eq.trans` rather than `rw`.
    exact (congrArg (fun c ↦ D (D c)) (twistedMorseChainProd_single_single L K p q a b).symm).trans
      (hB _ _)
  | add x y hx hy =>
    let F (P : criticalPoints 𝓘(ℝ, E × E') (f ∘ Prod.fst + g ∘ Prod.snd)) : Type w :=
      (L.externalTensor K).obj (FundamentalGroupoid.mk (P : M × N))
    rw [LinearMap.zero_apply] at hx hy ⊢
    exact (congrArg (D ∘ₗ D) (Pi.single_add (f := F) _ x y)).trans
      ((map_add _ _ _).trans (by rw [hx, hy, add_zero]))

end IsMorseSmale

end IsAdaptedPseudoGradient

end TauCeti
