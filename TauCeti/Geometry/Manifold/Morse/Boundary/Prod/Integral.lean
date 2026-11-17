/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Boundary.Integral
public import TauCeti.Geometry.Manifold.Morse.Boundary.Prod.Basic
public import TauCeti.Geometry.Manifold.Morse.Stable.Prod
import TauCeti.Geometry.Manifold.MFDeriv.Prod

/-!
# The integral Morse complex of a product manifold

Let `f` be a Morse function on a compact boundaryless manifold `M` and `X` a Morse–Smale
pseudo-gradient adapted to `f`, and likewise `g`, `Y` on `N`. The mod-two Morse complex of the
separated sum `f ∘ Prod.fst + g ∘ Prod.snd` on `M × N`, for the product field `(X, Y)`, is the
tensor product of the mod-two Morse complexes
(`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.morseChainProdEquiv_comp_morseBoundary`). This file
proves the integral version, with its Koszul sign.

Orientation data `𝔬` for `X` and `𝔬'` for `Y` (`TauCeti.MorseOrientation`) give product
orientation data `𝔬.prod 𝔬'` (`TauCeti.MorseOrientation.prod`): at `(p, q)` the product of the
Morse charts, with the orientation of the unstable manifold of `p` followed by that of `q`
(`TauCeti.MorseChart.prodOrientation`). With homological grading by the Morse index, the integral
Morse boundary of the product is then

`∂ (p ⊗ q) = ∂ p ⊗ q + (-1) ^ ind p p ⊗ ∂ q`

(`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.morseChainProdEquiv_comp_signedMorseBoundary`), over
every commutative ring of coefficients.

The trajectories of index one of the product are those of `X` with a constant second component
and those of `Y` with a constant first component
(`TauCeti.IsAdaptedPseudoGradient.morseTrajectorySlice_prod_right`,
`TauCeti.IsAdaptedPseudoGradient.morseTrajectorySlice_prod_left`). Their signs compare the product
orientation, transported by the unstable frame, with the direction of the flow followed by the
orientation at the end. The unstable frames and the normal coordinates of the product are the
products of those of the factors (`TauCeti.Geometry.Manifold.Morse.Stable.Prod`), so the comparison
map of the product is built from that of the moving factor and the identity of the constant one:

* along a trajectory of `X` from `p` to `p'`, it is the comparison map of `X` followed by the
  coordinates at `q`, and the sign is that of `X`
  (`TauCeti.IsAdaptedPseudoGradient.trajectorySign_prod_right`);
* along a trajectory of `Y` from `q` to `q'`, the direction of the flow must pass the `ind p`
  coordinates at `p` to come first, and the sign is `(-1) ^ ind p` times that of `Y`
  (`TauCeti.IsAdaptedPseudoGradient.trajectorySign_prod_left`).

## Main definitions

* `TauCeti.MorseChart.prodOrientation`: the product orientation of the coordinates of negative
  weight of a product of Morse charts.
* `TauCeti.MorseOrientation.prod`: orientation data on a product.

## Main results

* `TauCeti.IsAdaptedPseudoGradient.trajectorySign_prod_right` and
  `TauCeti.IsAdaptedPseudoGradient.trajectorySign_prod_left`: the signs of the trajectories of a
  product.
* `TauCeti.IsAdaptedPseudoGradient.signedMorseBoundaryCoeff_prod_right`,
  `TauCeti.IsAdaptedPseudoGradient.signedMorseBoundaryCoeff_prod_left` and
  `TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.signedMorseBoundaryCoeff_prod_of_ne`: the boundary
  coefficients of a product along each factor, and between pairs differing in both components.
* `TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.signedMorseBoundaryCoeff_prod`: the boundary
  coefficients of a product.
* `TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.morseChainProdEquiv_comp_signedMorseBoundary`: the
  integral Morse complex of a product is the tensor product complex, with the Koszul sign.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §2.3 (orientations of the descending manifolds and the signs
  of flow lines) and §3, Exercise 2 (the Morse complex of a product).
-/

public section

open Function Set
open scoped ContDiff Manifold

namespace TauCeti

variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E']
  [NormedSpace ℝ E'] {M N : Type*} [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace N]
  [ChartedSpace E' N]

attribute [local instance low] chartedSpaceProd

attribute [local instance] isManifold_chartedSpaceProd

/-! ### Orientations of the coordinates of negative weight of a product of Morse charts -/

namespace MorseChart

variable [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, E') ∞ N] {f : M → ℝ} {g : N → ℝ} {x : M}
  {y : N} (φ : MorseChart E f x) (ψ : MorseChart E' g y) [FiniteDimensional ℝ E]
  [FiniteDimensional ℝ E']

/-- **The product orientation of the coordinates of negative weight of a product of Morse
charts**: the orientation `op` of the coordinates of negative weight of `φ` followed by the
orientation `oq` of those of `ψ`. -/
noncomputable def prodOrientation
    (op : Orientation ℝ ({i // φ.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f x)))
    (oq : Orientation ℝ ({j // ψ.weight j < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E') g y))) :
    Orientation ℝ ({i // (φ.prod ψ).weight i < 0} → ℝ)
      (Fin (manifoldMorseIndex 𝓘(ℝ, E × E') (f ∘ Prod.fst + g ∘ Prod.snd) (x, y))) :=
  Orientation.map _ (φ.prodNegativeEquiv ψ).symm
    (Orientation.reindex ℝ _ (finCongr (manifoldMorseIndex_comp_fst_add_comp_snd_chartedSpaceProd
      ((φ.contMDiffAt φ.mem_source).of_le (by simp))
      ((ψ.contMDiffAt ψ.mem_source).of_le (by simp))).symm)
      (op.prod oq φ.finrank_negativeWeight_fun ψ.finrank_negativeWeight_fun))

variable {φ ψ}
  {op : Orientation ℝ ({i // φ.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f x))}
  {oq : Orientation ℝ ({j // ψ.weight j < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E') g y))}

/-- The product orientation, read in the pairs of coordinates of negative weight of the two
charts, is the product of the two orientations. -/
theorem map_prodNegativeEquiv_prodOrientation :
    Orientation.map _ (φ.prodNegativeEquiv ψ) (φ.prodOrientation ψ op oq) =
      Orientation.reindex ℝ _ (finCongr (manifoldMorseIndex_comp_fst_add_comp_snd_chartedSpaceProd
        ((φ.contMDiffAt φ.mem_source).of_le (by simp))
        ((ψ.contMDiffAt ψ.mem_source).of_le (by simp))).symm)
        (op.prod oq φ.finrank_negativeWeight_fun ψ.finrank_negativeWeight_fun) := by
  rw [prodOrientation, ← Orientation.map_trans, LinearEquiv.symm_trans_self, Orientation.map_refl]
  rfl

/-- Reversing the orientation of the first factor reverses the product orientation. -/
@[simp]
theorem prodOrientation_neg_left : φ.prodOrientation ψ (-op) oq = -φ.prodOrientation ψ op oq := by
  rw [prodOrientation, Orientation.prod_neg_left, Orientation.reindex_neg, Orientation.map_neg,
    prodOrientation]

/-- Reversing the orientation of the second factor reverses the product orientation. -/
@[simp]
theorem prodOrientation_neg_right : φ.prodOrientation ψ op (-oq) = -φ.prodOrientation ψ op oq := by
  rw [prodOrientation, Orientation.prod_neg_right, Orientation.reindex_neg, Orientation.map_neg,
    prodOrientation]

end MorseChart

/-! ### Comparison maps along trajectories of a product -/

namespace IsAdaptedPseudoGradient

variable [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, E') ∞ N] [FiniteDimensional ℝ E]
  [FiniteDimensional ℝ E'] [CompactSpace M] [T2Space M] [CompactSpace N] [T2Space N]
  {f : M → ℝ} {g : N → ℝ} {X : (z : M) → TangentSpace 𝓘(ℝ, E) z}
  {Y : (z : N) → TangentSpace 𝓘(ℝ, E') z} {hX : IsAdaptedPseudoGradient f X}
  {hY : IsAdaptedPseudoGradient g Y}

section SecondFactorConstant

variable {p p' : M} {q : N} {φp : MorseChart E f p} {φp' : MorseChart E f p'}
  {ψ : MorseChart E' g q}
  (hφp : ∀ z ∈ φp.toChart.source, φp.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φp.toChart z (X z)) =
    fun i ↦ -(φp.weight i * φp.coord (φp.toChart z) i))
  (hφp' : ∀ z ∈ φp'.toChart.source, φp'.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φp'.toChart z (X z)) =
    fun i ↦ -(φp'.weight i * φp'.coord (φp'.toChart z) i))
  (hψ : ∀ z ∈ ψ.toChart.source, ψ.coord (mfderiv 𝓘(ℝ, E') 𝓘(ℝ, E') ψ.toChart z (Y z)) =
    fun i ↦ -(ψ.weight i * ψ.coord (ψ.toChart z) i))
include hφp hφp' hψ

/-- **The comparison map along a trajectory of the first factor.** At a point `(y, q)` of a
trajectory of the product from `(p, q)` to `(p', q)`, with `q` a critical point of `g`, the
comparison map of the product charts sends the pair `(a, b)` of coordinates of negative weight to
the comparison of `a` along the trajectory of `X` through `y`, with `b` unchanged. At the critical
point `q` the normal coordinates of `W^s(q)` invert the unstable frame of `W^u(q)` and `g` has
vanishing differential. -/
theorem trajectoryComparison_prod_right (hf : IsMorse 𝓘(ℝ, E) f) (hg : IsMorse 𝓘(ℝ, E') g)
    (hq : q ∈ criticalPoints 𝓘(ℝ, E') g) {y : M}
    (hy : y ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet p') (a : {i // φp.weight i < 0} → ℝ)
    (b : {j // ψ.weight j < 0} → ℝ) :
    (hX.prod hY).trajectoryComparison (φp.prod ψ) (φp'.prod ψ) (y, q)
        ((φp.prodNegativeEquiv ψ).symm (a, b)) =
      ((hX.trajectoryComparison φp φp' y a).1,
        (φp'.prodNegativeEquiv ψ).symm ((hX.trajectoryComparison φp φp' y a).2, b)) := by
  have hqq := hY.mem_unstableSet_inter_stableSet_self
    (mem_criticalPoints_iff_mfderiv_eq_zero.1 hq)
  have hF := unstableFrame_prod_prodNegativeEquiv_symm hφp hψ hf hg hy.1 hqq.1 a b
  have hC := (hX.prod hY).trajectoryComparison_apply (φp.prod ψ) (φp'.prod ψ) (y, q)
    ((φp.prodNegativeEquiv ψ).symm (a, b))
  refine Prod.ext ?_ ?_
  · refine (congrArg Prod.fst hC).trans <|
      (congrArg (mvfderiv 𝓘(ℝ, E × E') (f ∘ Prod.fst + g ∘ Prod.snd) (y, q)) hF).trans ?_
    have hd := mvfderiv_comp_fst_add_comp_snd_apply (p := (y, q)) (hX.mdifferentiable y)
      (hY.mdifferentiable q) (hX.unstableFrame φp y a, hY.unstableFrame ψ q b)
    rw [← modelWithCornersSelf_prod, mem_criticalPoints.1 hq, zero_apply] at hd
    refine hd.trans ((add_zero _).trans ?_)
    rw [trajectoryComparison_apply]
  · refine (φp'.prodNegativeEquiv ψ).injective ?_
    refine (congrArg (fun c ↦ φp'.prodNegativeEquiv ψ c.2) hC).trans <|
      (congrArg (fun v ↦ φp'.prodNegativeEquiv ψ
        ((hX.prod hY).stableNormal (φp'.prod ψ) (y, q) v)) hF).trans ?_
    rw [prodNegativeEquiv_stableNormal_prod hφp' hψ hy.2 hqq.2, LinearEquiv.apply_symm_apply,
      stableNormal_unstableFrame_self hψ, trajectoryComparison_apply]

/-- **The signs of the trajectories of the first factor.** Along a trajectory of the product from
`(p, q)` to `(p', q)` through `(y, q)`, with `q` a critical point of `g`, the sign for the product
orientations is the sign of the trajectory of `X` through `y`: the comparison map of the product is
that of `X` times the identity of the coordinates of negative weight at `q`, so it carries the
product orientation to the product of the target orientation of `X` with that at `q`. -/
theorem trajectorySign_prod_right (hf : IsMorse 𝓘(ℝ, E) f) (hg : IsMorse 𝓘(ℝ, E') g)
    (hq : q ∈ criticalPoints 𝓘(ℝ, E') g) {y : M}
    (hy : y ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet p')
    (hC : Bijective (hX.trajectoryComparison φp φp' y))
    {op : Orientation ℝ ({i // φp.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f p))}
    {op' : Orientation ℝ ({i // φp'.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f p'))}
    {oq : Orientation ℝ ({j // ψ.weight j < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E') g q))}
    (hpp' : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f p' + 1)
    (hPP' : manifoldMorseIndex 𝓘(ℝ, E × E') (f ∘ Prod.fst + g ∘ Prod.snd) (p, q) =
      manifoldMorseIndex 𝓘(ℝ, E × E') (f ∘ Prod.fst + g ∘ Prod.snd) (p', q) + 1) :
    (hX.prod hY).trajectorySign (φp.prod ψ) (φp'.prod ψ) (φp.prodOrientation ψ op oq)
        (φp'.prodOrientation ψ op' oq) hPP' (y, q) =
      hX.trajectorySign φp φp' op op' hpp' y := by
  obtain ⟨u, hu, hmap⟩ :=
    exists_trajectorySign_eq_and_map_eq (op := op) (oq := op') (hpq := hpp') hC
  -- The comparison map of the product, as a composite of linear equivalences.
  set L := LinearEquiv.ofBijective _ hC
  set LP := (φp.prodNegativeEquiv ψ).trans ((L.prodCongr (LinearEquiv.refl ℝ _)).trans
    ((LinearEquiv.prodAssoc ℝ ℝ _ _).trans
      ((LinearEquiv.refl ℝ ℝ).prodCongr (φp'.prodNegativeEquiv ψ).symm))) with hLP_def
  have hLP (v) : LP v = (hX.prod hY).trajectoryComparison (φp.prod ψ) (φp'.prod ψ) (y, q) v := by
    obtain ⟨⟨a, b⟩, rfl⟩ := (φp.prodNegativeEquiv ψ).symm.surjective v
    rw [trajectoryComparison_prod_right (hX := hX) (hY := hY) hφp hφp' hψ hf hg hq hy a b]
    simp only [LP, L, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
      LinearEquiv.prodCongr_apply, LinearEquiv.ofBijective_apply]
    -- The identity of `ℝ` acts on a value of the differential of `f`, a vector of the tangent
    -- space of `ℝ`, which `LinearEquiv.refl_apply` does not see as an element of `ℝ`.
    rfl
  have hCP : Bijective ((hX.prod hY).trajectoryComparison (φp.prod ψ) (φp'.prod ψ) (y, q)) := by
    rw [← funext hLP]
    exact LP.bijective
  rw [hu]
  refine trajectorySign_eq_of_map_eq hCP ?_
  rw [show LinearEquiv.ofBijective _ hCP = LP from LinearEquiv.ext fun v ↦ (hLP v).symm]
  rw [hLP_def, Orientation.map_trans, MorseChart.map_prodNegativeEquiv_prodOrientation,
    Orientation.map_trans, Orientation.map_trans, Orientation.map_reindex, Orientation.map_prod,
    hmap, Orientation.map_refl, Equiv.refl_apply, Orientation.prod_units_smul_left,
    Orientation.reindex_units_smul, Orientation.map_units_smul, Orientation.map_units_smul]
  congr 1
  simp only [MorseChart.trajectoryTargetOrientation_def, MorseChart.prodOrientation,
    Orientation.prod_reindex_finCongr_left, Orientation.prod_reindex_finCongr_right,
    Orientation.map_reindex, Orientation.map_prodAssoc_prod, Orientation.map_prod,
    Orientation.map_refl, Equiv.refl_apply, Orientation.reindex_finCongr_reindex_finCongr]

end SecondFactorConstant

section FirstFactorConstant

variable {p : M} {q q' : N} {φ : MorseChart E f p} {ψq : MorseChart E' g q}
  {ψq' : MorseChart E' g q'}
  (hφ : ∀ z ∈ φ.toChart.source, φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart z (X z)) =
    fun i ↦ -(φ.weight i * φ.coord (φ.toChart z) i))
  (hψq : ∀ z ∈ ψq.toChart.source, ψq.coord (mfderiv 𝓘(ℝ, E') 𝓘(ℝ, E') ψq.toChart z (Y z)) =
    fun i ↦ -(ψq.weight i * ψq.coord (ψq.toChart z) i))
  (hψq' : ∀ z ∈ ψq'.toChart.source, ψq'.coord (mfderiv 𝓘(ℝ, E') 𝓘(ℝ, E') ψq'.toChart z (Y z)) =
    fun i ↦ -(ψq'.weight i * ψq'.coord (ψq'.toChart z) i))
include hφ hψq hψq'

/-- **The comparison map along a trajectory of the second factor.** At a point `(p, w)` of a
trajectory of the product from `(p, q)` to `(p, q')`, with `p` a critical point of `f`, the
comparison map of the product charts sends the pair `(a, b)` of coordinates of negative weight to
the comparison of `b` along the trajectory of `Y` through `w`, with `a` inserted after its
derivative component. -/
theorem trajectoryComparison_prod_left (hf : IsMorse 𝓘(ℝ, E) f) (hg : IsMorse 𝓘(ℝ, E') g)
    (hp : p ∈ criticalPoints 𝓘(ℝ, E) f) {w : N}
    (hw : w ∈ hY.flow.unstableSet q ∩ hY.flow.stableSet q') (a : {i // φ.weight i < 0} → ℝ)
    (b : {j // ψq.weight j < 0} → ℝ) :
    (hX.prod hY).trajectoryComparison (φ.prod ψq) (φ.prod ψq') (p, w)
        ((φ.prodNegativeEquiv ψq).symm (a, b)) =
      ((hY.trajectoryComparison ψq ψq' w b).1,
        (φ.prodNegativeEquiv ψq').symm (a, (hY.trajectoryComparison ψq ψq' w b).2)) := by
  have hpp := hX.mem_unstableSet_inter_stableSet_self
    (mem_criticalPoints_iff_mfderiv_eq_zero.1 hp)
  have hF := unstableFrame_prod_prodNegativeEquiv_symm hφ hψq hf hg hpp.1 hw.1 a b
  have hC := (hX.prod hY).trajectoryComparison_apply (φ.prod ψq) (φ.prod ψq') (p, w)
    ((φ.prodNegativeEquiv ψq).symm (a, b))
  refine Prod.ext ?_ ?_
  · refine (congrArg Prod.fst hC).trans <|
      (congrArg (mvfderiv 𝓘(ℝ, E × E') (f ∘ Prod.fst + g ∘ Prod.snd) (p, w)) hF).trans ?_
    have hd := mvfderiv_comp_fst_add_comp_snd_apply (p := (p, w)) (hX.mdifferentiable p)
      (hY.mdifferentiable w) (hX.unstableFrame φ p a, hY.unstableFrame ψq w b)
    rw [← modelWithCornersSelf_prod, mem_criticalPoints.1 hp, zero_apply] at hd
    refine hd.trans ((zero_add _).trans ?_)
    rw [trajectoryComparison_apply]
  · refine (φ.prodNegativeEquiv ψq').injective ?_
    refine (congrArg (fun c ↦ φ.prodNegativeEquiv ψq' c.2) hC).trans <|
      (congrArg (fun v ↦ φ.prodNegativeEquiv ψq'
        ((hX.prod hY).stableNormal (φ.prod ψq') (p, w) v)) hF).trans ?_
    rw [prodNegativeEquiv_stableNormal_prod hφ hψq' hpp.2 hw.2, LinearEquiv.apply_symm_apply,
      stableNormal_unstableFrame_self hφ, trajectoryComparison_apply]

/-- **The signs of the trajectories of the second factor.** Along a trajectory of the product from
`(p, q)` to `(p, q')` through `(p, w)`, with `p` a critical point of `f`, the sign for the product
orientations is `(-1) ^ ind p` times the sign of the trajectory of `Y` through `w`: the direction
of the flow, which comes first in the target orientation, passes the `ind p` directions of the
unstable manifold of `p`, which come first in the product orientation. -/
theorem trajectorySign_prod_left (hf : IsMorse 𝓘(ℝ, E) f) (hg : IsMorse 𝓘(ℝ, E') g)
    (hp : p ∈ criticalPoints 𝓘(ℝ, E) f) {w : N}
    (hw : w ∈ hY.flow.unstableSet q ∩ hY.flow.stableSet q')
    (hC : Bijective (hY.trajectoryComparison ψq ψq' w))
    {op : Orientation ℝ ({i // φ.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f p))}
    {oq : Orientation ℝ ({j // ψq.weight j < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E') g q))}
    {oq' : Orientation ℝ ({j // ψq'.weight j < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E') g q'))}
    (hqq' : manifoldMorseIndex 𝓘(ℝ, E') g q = manifoldMorseIndex 𝓘(ℝ, E') g q' + 1)
    (hPP' : manifoldMorseIndex 𝓘(ℝ, E × E') (f ∘ Prod.fst + g ∘ Prod.snd) (p, q) =
      manifoldMorseIndex 𝓘(ℝ, E × E') (f ∘ Prod.fst + g ∘ Prod.snd) (p, q') + 1) :
    (hX.prod hY).trajectorySign (φ.prod ψq) (φ.prod ψq') (φ.prodOrientation ψq op oq)
        (φ.prodOrientation ψq' op oq') hPP' (p, w) =
      (-1) ^ manifoldMorseIndex 𝓘(ℝ, E) f p * hY.trajectorySign ψq ψq' oq oq' hqq' w := by
  obtain ⟨u, hu, hmap⟩ :=
    exists_trajectorySign_eq_and_map_eq (op := oq) (oq := oq') (hpq := hqq') hC
  -- The comparison map of the product, as a composite of linear equivalences.
  set L := LinearEquiv.ofBijective _ hC
  set LP := (φ.prodNegativeEquiv ψq).trans (((LinearEquiv.refl ℝ _).prodCongr L).trans
    ((LinearEquiv.prodAssoc ℝ _ ℝ _).symm.trans
      (((LinearEquiv.prodComm ℝ _ ℝ).prodCongr (LinearEquiv.refl ℝ _)).trans
        ((LinearEquiv.prodAssoc ℝ ℝ _ _).trans
          ((LinearEquiv.refl ℝ ℝ).prodCongr (φ.prodNegativeEquiv ψq').symm))))) with hLP_def
  have hLP (v) : LP v = (hX.prod hY).trajectoryComparison (φ.prod ψq) (φ.prod ψq') (p, w) v := by
    obtain ⟨⟨a, b⟩, rfl⟩ := (φ.prodNegativeEquiv ψq).symm.surjective v
    rw [trajectoryComparison_prod_left (hX := hX) (hY := hY) hφ hψq hψq' hf hg hp hw a b]
    simp only [LP, L, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
      LinearEquiv.prodCongr_apply, LinearEquiv.ofBijective_apply]
    rfl
  have hCP : Bijective ((hX.prod hY).trajectoryComparison (φ.prod ψq) (φ.prod ψq') (p, w)) := by
    rw [← funext hLP]
    exact LP.bijective
  have hunit : ((-1) ^ manifoldMorseIndex 𝓘(ℝ, E) f p * hY.trajectorySign ψq ψq' oq oq' hqq' w) =
      (((-1) ^ manifoldMorseIndex 𝓘(ℝ, E) f p * u : ℤˣ) : ℤ) := by
    rw [hu]
    push_cast
    rfl
  rw [hunit]
  refine trajectorySign_eq_of_map_eq hCP ?_
  rw [show LinearEquiv.ofBijective _ hCP = LP from LinearEquiv.ext fun v ↦ (hLP v).symm]
  rw [hLP_def, Orientation.map_trans, MorseChart.map_prodNegativeEquiv_prodOrientation,
    Orientation.map_trans, Orientation.map_trans, Orientation.map_trans, Orientation.map_trans,
    Orientation.map_reindex, Orientation.map_prod, hmap, Orientation.map_refl, Equiv.refl_apply,
    Orientation.prod_units_smul_right, Orientation.reindex_units_smul,
    Orientation.map_units_smul, Orientation.map_units_smul, Orientation.map_units_smul,
    Orientation.map_units_smul, show ((-1) ^ manifoldMorseIndex 𝓘(ℝ, E) f p * u : ℤˣ) =
      u * (-1) ^ manifoldMorseIndex 𝓘(ℝ, E) f p from mul_comm _ _, map_mul, mul_smul]
  congr 1
  have hk : Units.map (Int.castRingHom ℝ).toMonoidHom ((-1) ^ manifoldMorseIndex 𝓘(ℝ, E) f p) =
      (-1 : ℝˣ) ^ (manifoldMorseIndex 𝓘(ℝ, E) f p * 1) := by
    ext
    simp
  rw [hk, ψq'.trajectoryTargetOrientation_def, Orientation.prod_reindex_finCongr_right,
    Orientation.reindex_finCongr_reindex_finCongr, Orientation.map_reindex,
    Orientation.map_prodAssoc_symm_prod]
  simp only [Orientation.map_reindex, Orientation.reindex_finCongr_reindex_finCongr]
  rw [Orientation.map_prod, Orientation.map_prodComm_prod, Orientation.map_refl, Equiv.refl_apply,
    Orientation.prod_units_smul_left]
  simp only [Orientation.map_units_smul, Orientation.reindex_units_smul]
  congr 1
  simp only [MorseChart.trajectoryTargetOrientation_def, MorseChart.prodOrientation,
    Orientation.prod_reindex_finCongr_left, Orientation.prod_reindex_finCongr_right,
    Orientation.map_reindex, Orientation.map_prodAssoc_prod, Orientation.map_prod,
    Orientation.map_refl, Equiv.refl_apply, Orientation.reindex_finCongr_reindex_finCongr]

end FirstFactorConstant

end IsAdaptedPseudoGradient

/-! ### Orientation data on a product -/

namespace MorseOrientation

variable [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, E') ∞ N] [FiniteDimensional ℝ E]
  [FiniteDimensional ℝ E'] {f : M → ℝ} {g : N → ℝ} {X : (z : M) → TangentSpace 𝓘(ℝ, E) z}
  {Y : (z : N) → TangentSpace 𝓘(ℝ, E') z} (𝔬 : MorseOrientation f X) (𝔬' : MorseOrientation g Y)
  (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f) (hg : MDifferentiable 𝓘(ℝ, E') 𝓘(ℝ) g)

/-- **Orientation data on a product.** At the critical point `(p, q)` of the separated sum, the
product of the Morse charts of `𝔬` at `p` and of `𝔬'` at `q`, in which the product field is
linear, with the orientation of `𝔬` at `p` followed by that of `𝔬'` at `q`: the unstable manifold
`W^u(p) × W^u(q)` is oriented by `W^u(p)` followed by `W^u(q)`. -/
-- The body is exposed: the type of `orientation` depends on `chart`, and stating
-- `prod_orientation` needs `(𝔬.prod 𝔬' hf hg).chart` to reduce to the product of charts.
@[expose]
noncomputable def prod :
    MorseOrientation (f ∘ Prod.fst + g ∘ Prod.snd) (Manifold.prodVectorField X Y) where
  chart P := (𝔬.chart (criticalPointsCompFstAddCompSndEquiv f g hf hg P).1).prod
    (𝔬'.chart (criticalPointsCompFstAddCompSndEquiv f g hf hg P).2)
  coord_mfderiv_chart P := MorseChart.forall_coord_mfderiv_prod _ _
    (𝔬.coord_mfderiv_chart (criticalPointsCompFstAddCompSndEquiv f g hf hg P).1)
    (𝔬'.coord_mfderiv_chart (criticalPointsCompFstAddCompSndEquiv f g hf hg P).2)
  orientation P := (𝔬.chart _).prodOrientation (𝔬'.chart _)
    (𝔬.orientation (criticalPointsCompFstAddCompSndEquiv f g hf hg P).1)
    (𝔬'.orientation (criticalPointsCompFstAddCompSndEquiv f g hf hg P).2)

/-- The Morse chart of the product orientation data at `(p, q)` is the product of the charts. -/
theorem prod_chart (p : criticalPoints 𝓘(ℝ, E) f) (q : criticalPoints 𝓘(ℝ, E') g) :
    (𝔬.prod 𝔬' hf hg).chart ((criticalPointsCompFstAddCompSndEquiv f g hf hg).symm (p, q)) =
      (𝔬.chart p).prod (𝔬'.chart q) :=
  (rfl)

/-- The orientation of the product orientation data at `(p, q)` is the product orientation. -/
theorem prod_orientation (p : criticalPoints 𝓘(ℝ, E) f) (q : criticalPoints 𝓘(ℝ, E') g) :
    (𝔬.prod 𝔬' hf hg).orientation ((criticalPointsCompFstAddCompSndEquiv f g hf hg).symm (p, q)) =
      (𝔬.chart p).prodOrientation (𝔬'.chart q) (𝔬.orientation p) (𝔬'.orientation q) :=
  (rfl)

end MorseOrientation

/-! ### The integral Morse boundary of a product -/

namespace IsAdaptedPseudoGradient

variable [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, E') ∞ N] [FiniteDimensional ℝ E]
  [FiniteDimensional ℝ E'] [CompactSpace M] [T2Space M] [CompactSpace N] [T2Space N]
  {f : M → ℝ} {g : N → ℝ} {X : (z : M) → TangentSpace 𝓘(ℝ, E) z}
  {Y : (z : N) → TangentSpace 𝓘(ℝ, E') z} (hX : IsAdaptedPseudoGradient f X)
  (hY : IsAdaptedPseudoGradient g Y) (hf : IsMorse 𝓘(ℝ, E) f) (hg : IsMorse 𝓘(ℝ, E') g)
  (𝔬 : MorseOrientation f X) (𝔬' : MorseOrientation g Y)
include hf hg

omit [CompactSpace M] [T2Space M] [CompactSpace N] [T2Space N] in
/-- The Morse index of the separated sum at `(p, q)` is the sum of the indices. -/
private theorem manifoldMorseIndex_criticalPointsCompFstAddCompSndEquiv_symm
    (p : criticalPoints 𝓘(ℝ, E) f) (q : criticalPoints 𝓘(ℝ, E') g) :
    manifoldMorseIndex 𝓘(ℝ, E × E') (f ∘ Prod.fst + g ∘ Prod.snd)
        ((criticalPointsCompFstAddCompSndEquiv f g hX.mdifferentiable hY.mdifferentiable).symm
          (p, q) : M × N) =
      manifoldMorseIndex 𝓘(ℝ, E) f p + manifoldMorseIndex 𝓘(ℝ, E') g q :=
  manifoldMorseIndex_comp_fst_add_comp_snd_chartedSpaceProd
    ((hf.contMDiff _).of_le (by norm_num)) ((hg.contMDiff _).of_le (by norm_num))

/-- **The boundary coefficients of a product along the second factor.** The coefficient of
`(p, q')` in the integral Morse boundary of `(p, q)` is the coefficient of `q'` in the boundary of
`q`, multiplied by the Koszul sign `(-1) ^ ind p`: the trajectories are those of `Y`, and the
direction of the flow passes the `ind p` directions of `W^u(p)` in the product orientation. -/
theorem signedMorseBoundaryCoeff_prod_left (hYs : hY.IsMorseSmale) (p : criticalPoints 𝓘(ℝ, E) f)
    (q q' : criticalPoints 𝓘(ℝ, E') g) :
    (hX.prod hY).signedMorseBoundaryCoeff (𝔬.prod 𝔬' hX.mdifferentiable hY.mdifferentiable)
        ((criticalPointsCompFstAddCompSndEquiv f g hX.mdifferentiable hY.mdifferentiable).symm
          (p, q))
        ((criticalPointsCompFstAddCompSndEquiv f g hX.mdifferentiable hY.mdifferentiable).symm
          (p, q')) =
      (-1) ^ manifoldMorseIndex 𝓘(ℝ, E) f p * hY.signedMorseBoundaryCoeff 𝔬' q q' := by
  set e := criticalPointsCompFstAddCompSndEquiv f g hX.mdifferentiable hY.mdifferentiable
  have hindP := manifoldMorseIndex_criticalPointsCompFstAddCompSndEquiv_symm hX hY hf hg p q
  have hindQ := manifoldMorseIndex_criticalPointsCompFstAddCompSndEquiv_symm hX hY hf hg p q'
  by_cases hqq' : manifoldMorseIndex 𝓘(ℝ, E') g q = manifoldMorseIndex 𝓘(ℝ, E') g q' + 1
  swap
  · rw [signedMorseBoundaryCoeff_eq_zero_of_morseIndex_ne_add_one hqq', mul_zero]
    exact signedMorseBoundaryCoeff_eq_zero_of_morseIndex_ne_add_one (hX := hX.prod hY)
      (by rw [hindP, hindQ]; omega)
  have hPQ :
      manifoldMorseIndex 𝓘(ℝ, E × E') (f ∘ Prod.fst + g ∘ Prod.snd) (e.symm (p, q) : M × N) =
        manifoldMorseIndex 𝓘(ℝ, E × E') (f ∘ Prod.fst + g ∘ Prod.snd) (e.symm (p, q') : M × N) +
          1 := by
    rw [hindP, hindQ, hqq', add_assoc]
  have hS : (hX.prod hY).morseTrajectorySlice (e.symm (p, q) : M × N) (e.symm (p, q') : M × N) =
      (fun w ↦ ((p : M), w)) '' hY.morseTrajectorySlice q q' :=
    hX.morseTrajectorySlice_prod_left hY p.2 q q'
  -- The product field has its tangent spaces for the model `𝓘(ℝ, E).prod 𝓘(ℝ, E')`, so `rw`
  -- cannot rewrite the coefficients and counts of the product; `Eq.trans` chains the formulas.
  refine (signedMorseBoundaryCoeff_of_morseIndex_eq_add_one (hX := hX.prod hY)
    (𝔬 := 𝔬.prod 𝔬' hX.mdifferentiable hY.mdifferentiable) hPQ).trans <|
    (signedTrajectoryCount_def ..).trans <| (finsum_mem_congr hS fun _ _ ↦ rfl).trans <|
      (finsum_mem_image (Prod.mk_right_injective _).injOn).trans ?_
  rw [signedMorseBoundaryCoeff_of_morseIndex_eq_add_one hqq', signedTrajectoryCount_def,
    mul_finsum_mem]
  refine finsum_mem_congr rfl fun w hw ↦ ?_
  obtain ⟨hu, hs, -⟩ := hY.mem_morseTrajectorySlice.1 hw
  exact trajectorySign_prod_left (hX := hX) (hY := hY) (𝔬.coord_mfderiv_chart p)
    (𝔬'.coord_mfderiv_chart q) (𝔬'.coord_mfderiv_chart q') hf hg p.2 ⟨hu, hs⟩
    (bijective_trajectoryComparison (𝔬'.coord_mfderiv_chart q) (𝔬'.coord_mfderiv_chart q') hYs
      hg hqq' ⟨hu, hs⟩) hqq' hPQ

/-- **The boundary coefficients of a product along the first factor.** The coefficient of
`(p', q)` in the integral Morse boundary of `(p, q)` is the coefficient of `p'` in the boundary of
`p`: the trajectories are those of `X`, with the same signs. -/
theorem signedMorseBoundaryCoeff_prod_right (hXs : hX.IsMorseSmale)
    (p p' : criticalPoints 𝓘(ℝ, E) f)
    (q : criticalPoints 𝓘(ℝ, E') g) :
    (hX.prod hY).signedMorseBoundaryCoeff (𝔬.prod 𝔬' hX.mdifferentiable hY.mdifferentiable)
        ((criticalPointsCompFstAddCompSndEquiv f g hX.mdifferentiable hY.mdifferentiable).symm
          (p, q))
        ((criticalPointsCompFstAddCompSndEquiv f g hX.mdifferentiable hY.mdifferentiable).symm
          (p', q)) =
      hX.signedMorseBoundaryCoeff 𝔬 p p' := by
  set e := criticalPointsCompFstAddCompSndEquiv f g hX.mdifferentiable hY.mdifferentiable
  have hindP := manifoldMorseIndex_criticalPointsCompFstAddCompSndEquiv_symm hX hY hf hg p q
  have hindQ := manifoldMorseIndex_criticalPointsCompFstAddCompSndEquiv_symm hX hY hf hg p' q
  by_cases hpp' : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f p' + 1
  swap
  · rw [signedMorseBoundaryCoeff_eq_zero_of_morseIndex_ne_add_one hpp']
    exact signedMorseBoundaryCoeff_eq_zero_of_morseIndex_ne_add_one (hX := hX.prod hY)
      (by rw [hindP, hindQ]; omega)
  have hPQ :
      manifoldMorseIndex 𝓘(ℝ, E × E') (f ∘ Prod.fst + g ∘ Prod.snd) (e.symm (p, q) : M × N) =
        manifoldMorseIndex 𝓘(ℝ, E × E') (f ∘ Prod.fst + g ∘ Prod.snd) (e.symm (p', q) : M × N) +
          1 := by
    rw [hindP, hindQ, hpp']
    ring
  have hS : (hX.prod hY).morseTrajectorySlice (e.symm (p, q) : M × N) (e.symm (p', q) : M × N) =
      (fun y ↦ (y, (q : N))) '' hX.morseTrajectorySlice p p' :=
    hX.morseTrajectorySlice_prod_right hY q.2 p p'
  -- As in `signedMorseBoundaryCoeff_prod_left`, `Eq.trans` chains the formulas for the product.
  refine (signedMorseBoundaryCoeff_of_morseIndex_eq_add_one (hX := hX.prod hY)
    (𝔬 := 𝔬.prod 𝔬' hX.mdifferentiable hY.mdifferentiable) hPQ).trans <|
    (signedTrajectoryCount_def ..).trans <| (finsum_mem_congr hS fun _ _ ↦ rfl).trans <|
      (finsum_mem_image (Prod.mk_left_injective _).injOn).trans ?_
  rw [signedMorseBoundaryCoeff_of_morseIndex_eq_add_one hpp', signedTrajectoryCount_def]
  refine finsum_mem_congr rfl fun y hy ↦ ?_
  obtain ⟨hu, hs, -⟩ := hX.mem_morseTrajectorySlice.1 hy
  exact trajectorySign_prod_right (hX := hX) (hY := hY) (𝔬.coord_mfderiv_chart p)
    (𝔬.coord_mfderiv_chart p') (𝔬'.coord_mfderiv_chart q) hf hg q.2 ⟨hu, hs⟩
    (bijective_trajectoryComparison (𝔬.coord_mfderiv_chart p) (𝔬.coord_mfderiv_chart p') hXs
      hf hpp' ⟨hu, hs⟩) hpp' hPQ

namespace IsMorseSmale

variable {hX hY}

/-- **No boundary coefficient of a product moves both components.** For `p ≠ p'` and `q ≠ q'`,
the coefficient of `(p', q')` in the integral Morse boundary of `(p, q)` vanishes: a trajectory
between them would lower the index of each factor by at least one. -/
theorem signedMorseBoundaryCoeff_prod_of_ne (hXs : hX.IsMorseSmale) (hYs : hY.IsMorseSmale)
    {p p' : criticalPoints 𝓘(ℝ, E) f}
    {q q' : criticalPoints 𝓘(ℝ, E') g} (hpp : p ≠ p') (hqq : q ≠ q') :
    (hX.prod hY).signedMorseBoundaryCoeff (𝔬.prod 𝔬' hX.mdifferentiable hY.mdifferentiable)
        ((criticalPointsCompFstAddCompSndEquiv f g hX.mdifferentiable hY.mdifferentiable).symm
          (p, q))
        ((criticalPointsCompFstAddCompSndEquiv f g hX.mdifferentiable hY.mdifferentiable).symm
          (p', q')) = 0 := by
  have hindP := manifoldMorseIndex_criticalPointsCompFstAddCompSndEquiv_symm hX hY hf hg p q
  have hindQ := manifoldMorseIndex_criticalPointsCompFstAddCompSndEquiv_symm hX hY hf hg p' q'
  by_cases hind : manifoldMorseIndex 𝓘(ℝ, E) f p + manifoldMorseIndex 𝓘(ℝ, E') g q =
    manifoldMorseIndex 𝓘(ℝ, E) f p' + manifoldMorseIndex 𝓘(ℝ, E') g q' + 1
  · refine (signedMorseBoundaryCoeff_of_morseIndex_eq_add_one (hX := hX.prod hY)
      (𝔬 := 𝔬.prod 𝔬' hX.mdifferentiable hY.mdifferentiable)
      (by rw [hindP, hindQ]; exact hind)).trans <|
      (signedTrajectoryCount_def ..).trans <| (finsum_mem_congr
        (hXs.morseTrajectorySlice_prod_eq_empty hYs hf hg (fun h ↦ hpp (Subtype.ext h))
          (fun h ↦ hqq (Subtype.ext h)) hind.le) fun _ _ ↦ rfl).trans ?_
    exact finsum_mem_empty
  · exact signedMorseBoundaryCoeff_eq_zero_of_morseIndex_ne_add_one (hX := hX.prod hY)
      (by rw [hindP, hindQ]; exact hind)

open scoped Classical in
/-- **The integral Morse boundary coefficients of a product.** For Morse–Smale pseudo-gradients
`X` and `Y` and the product orientation data, the coefficient of `(p', q')` in the integral Morse
boundary of `(p, q)` is `(-1) ^ ind p` times the coefficient of `q'` in the boundary of `q` when
`p = p'`, plus the coefficient of `p'` in the boundary of `p` when `q = q'`. -/
theorem signedMorseBoundaryCoeff_prod (hXs : hX.IsMorseSmale) (hYs : hY.IsMorseSmale)
    (p p' : criticalPoints 𝓘(ℝ, E) f)
    (q q' : criticalPoints 𝓘(ℝ, E') g) :
    (hX.prod hY).signedMorseBoundaryCoeff (𝔬.prod 𝔬' hX.mdifferentiable hY.mdifferentiable)
        ((criticalPointsCompFstAddCompSndEquiv f g hX.mdifferentiable hY.mdifferentiable).symm
          (p, q))
        ((criticalPointsCompFstAddCompSndEquiv f g hX.mdifferentiable hY.mdifferentiable).symm
          (p', q')) =
      (if p = p' then
          (-1) ^ manifoldMorseIndex 𝓘(ℝ, E) f p * hY.signedMorseBoundaryCoeff 𝔬' q q'
        else 0) +
        if q = q' then hX.signedMorseBoundaryCoeff 𝔬 p p' else 0 := by
  by_cases hpp : p = p'
  · subst hpp
    rw [ite_eq_left rfl, hX.signedMorseBoundaryCoeff_prod_left hY hf hg 𝔬 𝔬' hYs]
    split_ifs with hqq
    · rw [signedMorseBoundaryCoeff_eq_zero_of_morseIndex_ne_add_one (hX := hX) (p := p) (q := p)
        (by omega), add_zero]
    · rw [add_zero]
  by_cases hqq : q = q'
  · subst hqq
    rw [ite_eq_right hpp, ite_eq_left rfl, zero_add,
      hX.signedMorseBoundaryCoeff_prod_right hY hf hg 𝔬 𝔬' hXs]
  · rw [ite_eq_right hpp, ite_eq_right hqq, add_zero,
      hXs.signedMorseBoundaryCoeff_prod_of_ne hf hg 𝔬 𝔬' hYs hpp hqq]

/-- **The integral Morse complex of a product is the tensor product complex.** For Morse–Smale
pseudo-gradients `X` and `Y`, the product orientation data and any commutative ring `R`, under the
identification of the Morse chains of `M × N` with the tensor product of the chains of `M` and of
`N`, the Morse boundary of the product field `(X, Y)` is `∂ ⊗ 1 + ε ⊗ ∂`, where `ε` multiplies a
critical point `p` by the Koszul sign `(-1) ^ ind p`: on chains,
`∂ (p ⊗ q) = ∂ p ⊗ q + (-1) ^ ind p p ⊗ ∂ q`. -/
theorem morseChainProdEquiv_comp_signedMorseBoundary (hXs : hX.IsMorseSmale)
    (hYs : hY.IsMorseSmale) (R : Type*) [CommRing R] :
    (morseChainProdEquiv f g R hX.mdifferentiable hY.mdifferentiable).toLinearMap ∘ₗ
        (hX.prod hY).signedMorseBoundary (𝔬.prod 𝔬' hX.mdifferentiable hY.mdifferentiable)
          (hf.comp_fst_add_comp_snd_chartedSpaceProd hg) R =
      ((hX.signedMorseBoundary 𝔬 hf R).rTensor (criticalPoints 𝓘(ℝ, E') g →₀ R) +
          TensorProduct.map
            (Finsupp.signEquiv (A := R) R
              fun p : criticalPoints 𝓘(ℝ, E) f ↦ (-1) ^ manifoldMorseIndex 𝓘(ℝ, E) f p).toLinearMap
            (hY.signedMorseBoundary 𝔬' hg R)) ∘ₗ
        (morseChainProdEquiv f g R hX.mdifferentiable hY.mdifferentiable).toLinearMap := by
  classical
  rw [morseChainProdEquiv_def]
  refine domLCongr_trans_finsuppTensorFinsupp'_symm_comp_eq_rTensor_add_map _ _ _ _ _
    fun p p' q q' ↦ ?_
  -- As in `signedMorseBoundaryCoeff_prod`, the coefficients of the product are rewritten through
  -- `Eq.trans` rather than `rw`.
  refine (signedMorseBoundary_single_apply (hX := hX.prod hY)
    (𝔬 := 𝔬.prod 𝔬' hX.mdifferentiable hY.mdifferentiable)
    (hf.comp_fst_add_comp_snd_chartedSpaceProd hg) _ _ _).trans <|
    (one_mul _).trans <| (congrArg (Int.cast : ℤ → R)
      (hXs.signedMorseBoundaryCoeff_prod hf hg 𝔬 𝔬' hYs p p' q q')).trans ?_
  by_cases hpp : p = p' <;> by_cases hqq : q = q' <;>
    simp [hpp, hqq, signedMorseBoundary_single_apply]

end IsMorseSmale

end IsAdaptedPseudoGradient

end TauCeti
