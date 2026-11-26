/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Measure.BaseChange.Basic
public import TauCeti.NumberTheory.Padics.Measure.CompletedGroupAlgebra.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.CompletedGroupAlgebra.BaseChange
import Mathlib.Topology.Algebra.Module.Compact
import TauCeti.Topology.Algebra.Ring.Basic

/-!
# Finite free `O`-valued measures and completed group algebras

For a compact, locally compact group `Γ` and a finite free Hausdorff topological `R`-algebra `O`
over a compact commutative ring `R` with continuous `R`-action (`ContinuousSMul R O`), the
comparison homomorphism `AbstractMeasure.toCompletedGroupAlgebra : D(Γ, ·) →ₐ[·] ·[[Γ]]` intertwines
scalar retraction `AbstractMeasure.mapScalars`, scalar extension `AbstractMeasure.extendScalars`,
and finite free measure base change `AbstractMeasure.baseChangeAlgEquiv` with the corresponding maps
`completedGroupAlgebra.mapAddMonoidHom`, `completedGroupAlgebra.mapRingHom`, and
`completedGroupAlgebra.baseChangeEquiv` on the completed group algebra.

When `Γ` is a profinite group and `R = ℤ_p`, combining `AbstractMeasure.baseChangeAlgEquiv O` with
`completedGroupAlgebra.baseChangeEquiv ℤ_[p] O Γ` and the integral-measure isomorphism
`AbstractMeasure.completedGroupAlgebraEquiv : D(Γ, ℤ_[p]) ≃ₐ[ℤ_[p]] ℤ_[p][[Γ]]` proves that
`toCompletedGroupAlgebra : D(Γ, O) →ₐ[O] O[[Γ]]` is an isomorphism of `O`-algebras
(`AbstractMeasure.completedGroupAlgebraEquivOfFreeOfFinite`, Rodrigues Jacinto–Williams,
Proposition 3.16). When `O` is moreover a normed commutative ring, this isomorphism is a
homeomorphism from the weak topology on `D(Γ, O)` to the inverse-limit topology on `O[[Γ]]`,
making `(D(Γ, O), WeakTopology)` a compact topological ring.

## Main definitions

* `AbstractMeasure.completedGroupAlgebraEquivOfFreeOfFinite p O`: the `O`-algebra isomorphism
  `D(Γ, O) ≃ₐ[O] completedGroupAlgebra O Γ` for a profinite group `Γ` and a finite free Hausdorff
  topological `ℤ_p`-algebra `O` with continuous `ℤ_p`-action (`ContinuousSMul ℤ_[p] O`).

## Main results

* `AbstractMeasure.toCompletedGroupAlgebra_mapScalars`,
  `AbstractMeasure.toCompletedGroupAlgebra_extendScalars`,
  `AbstractMeasure.toCompletedGroupAlgebra_baseChangeAlgEquiv`: compatibility of
  `toCompletedGroupAlgebra` with scalar retraction, scalar extension, and finite free base change.
* `AbstractMeasure.toCompletedGroupAlgebra_surjective_of_free_of_finite`,
  `AbstractMeasure.completedGroupAlgebraEquivOfFreeOfFinite_symm_of`,
  `AbstractMeasure.completedGroupAlgebraEquivOfFreeOfFinite_symm_mapRingHom`,
  `AbstractMeasure.completedGroupAlgebraEquivOfFreeOfFinite_symm_apply`.
* `AbstractMeasure.isHomeomorph_toCompletedGroupAlgebra_weak_of_free_of_finite`,
  `AbstractMeasure.isTopologicalRing_weak_of_free_of_finite`,
  `AbstractMeasure.compactSpace_weak_of_free_of_finite`.

## References

* J. Rodrigues Jacinto and C. Williams,
  [*An introduction to p-adic L-functions*](https://doi.org/10.2140/ent.2025.4.101),
  Essential Number Theory **4** (2025), no. 1, 101–216, §3.3, Proposition 3.16.
-/

public noncomputable section

open ContinuousMap TauCeti
open scoped TensorProduct

namespace AbstractMeasure

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [CompactSpace Γ]

section CompactGroup

variable {R O : Type*} [ContinuousMul Γ] [LocallyCompactSpace Γ]
  [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [CompactSpace R]
  [CommRing O] [TopologicalSpace O] [IsTopologicalRing O] [T2Space O]
  [Algebra R O] [ContinuousSMul R O] [Module.Free R O] [Module.Finite R O]

omit [Module.Free R O] in
/-- `toCompletedGroupAlgebra` intertwines `mapScalars l` on measures with
`completedGroupAlgebra.mapAddMonoidHom` along `l.toAddMonoidHom`. -/
@[simp]
theorem toCompletedGroupAlgebra_mapScalars (l : O →ₗ[R] R) (ν : D(Γ, O)) :
    toCompletedGroupAlgebra (mapScalars l ν) =
      completedGroupAlgebra.mapAddMonoidHom Γ l.toAddMonoidHom (toCompletedGroupAlgebra ν) := by
  ext U a
  rw [completedGroupAlgebra.coeff_proj_mapAddMonoidHom, proj_toCompletedGroupAlgebra,
    proj_toCompletedGroupAlgebra, ContinuousMonoidHom.finiteProjectionAlgHom_coeff,
    ContinuousMonoidHom.finiteProjectionAlgHom_coeff, finiteProjection_mapScalars,
    Finsupp.mapRange_apply, LinearMap.toAddMonoidHom_coe]

/-- `toCompletedGroupAlgebra` intertwines `extendScalars O` on measures with
`completedGroupAlgebra.mapRingHom` along `algebraMap R O`. -/
@[simp]
theorem toCompletedGroupAlgebra_extendScalars (μ : D(Γ, R)) :
    toCompletedGroupAlgebra (extendScalars O μ) =
      completedGroupAlgebra.mapRingHom Γ (algebraMap R O) (toCompletedGroupAlgebra μ) := by
  ext U a
  rw [completedGroupAlgebra.coeff_proj_mapRingHom, proj_toCompletedGroupAlgebra,
    proj_toCompletedGroupAlgebra, ContinuousMonoidHom.finiteProjectionAlgHom_coeff,
    ContinuousMonoidHom.finiteProjectionAlgHom_coeff, finiteProjection_extendScalars,
    Finsupp.mapRange_apply]

/-- `toCompletedGroupAlgebra` intertwines `baseChangeAlgEquiv O` on `O ⊗[R] D(Γ, R)` with
`completedGroupAlgebra.baseChangeEquiv R O Γ` on `O ⊗[R] R[[Γ]]`. -/
theorem toCompletedGroupAlgebra_baseChangeAlgEquiv (z : O ⊗[R] D(Γ, R)) :
    toCompletedGroupAlgebra (baseChangeAlgEquiv O z) =
      completedGroupAlgebra.baseChangeEquiv R O Γ
        (Algebra.TensorProduct.map (AlgHom.id O O) toCompletedGroupAlgebra z) := by
  refine TensorProduct.inductionOn z ?_ fun z₁ z₂ hz₁ hz₂ ↦ by
    rw [map_add, map_add, map_add, map_add, hz₁, hz₂]
  intro a μ
  simp

end CompactGroup

section ProfinitePadicInt

variable [IsTopologicalGroup Γ] [TotallyDisconnectedSpace Γ]

/-- **Surjectivity of `toCompletedGroupAlgebra` for finite free Hausdorff `ℤ_p`-algebras.** For a
profinite group `Γ` and a Hausdorff topological commutative `ℤ_p`-algebra `O` that is finite and
free over `ℤ_p` with continuous `ℤ_p`-action (`ContinuousSMul ℤ_[p] O`), every element of `O[[Γ]]`
arises from an `O`-valued measure on `Γ`. -/
theorem toCompletedGroupAlgebra_surjective_of_free_of_finite (p : ℕ) [Fact p.Prime]
    (O : Type*) [CommRing O] [TopologicalSpace O] [IsTopologicalRing O] [T2Space O]
    [Algebra ℤ_[p] O] [ContinuousSMul ℤ_[p] O] [Module.Free ℤ_[p] O] [Module.Finite ℤ_[p] O] :
    Function.Surjective
      (toCompletedGroupAlgebra : D(Γ, O) →ₐ[O] completedGroupAlgebra O Γ) := by
  intro y
  let e : O ⊗[ℤ_[p]] D(Γ, ℤ_[p]) ≃ₐ[O] O ⊗[ℤ_[p]] completedGroupAlgebra ℤ_[p] Γ :=
    Algebra.TensorProduct.congr (AlgEquiv.refl : O ≃ₐ[O] O)
      (completedGroupAlgebraEquiv (Γ := Γ) (p := p))
  refine ⟨baseChangeAlgEquiv O (e.symm ((completedGroupAlgebra.baseChangeEquiv ℤ_[p] O Γ).symm y)),
    ?_⟩
  rw [toCompletedGroupAlgebra_baseChangeAlgEquiv, ← toAlgHom_completedGroupAlgebraEquiv (p := p),
    ← AlgEquiv.refl_toAlgHom, ← Algebra.TensorProduct.congr_apply, e.apply_symm_apply,
    AlgEquiv.apply_symm_apply]

/-- **`O`-valued measures are the completed group algebra (Rodrigues Jacinto–Williams,
Proposition 3.16).** For a profinite group `Γ` and a Hausdorff topological commutative
`ℤ_p`-algebra `O` that is finite and free over `ℤ_p` with continuous `ℤ_p`-action, `D(Γ, O)` is
canonically isomorphic as an `O`-algebra to `O[[Γ]]`. -/
def completedGroupAlgebraEquivOfFreeOfFinite (p : ℕ) [Fact p.Prime]
    (O : Type*) [CommRing O] [TopologicalSpace O] [IsTopologicalRing O] [T2Space O]
    [Algebra ℤ_[p] O] [ContinuousSMul ℤ_[p] O] [Module.Free ℤ_[p] O] [Module.Finite ℤ_[p] O] :
    D(Γ, O) ≃ₐ[O] completedGroupAlgebra O Γ :=
  AlgEquiv.ofBijective toCompletedGroupAlgebra
    ⟨toCompletedGroupAlgebra_injective, toCompletedGroupAlgebra_surjective_of_free_of_finite p O⟩

/-- The forward map of `completedGroupAlgebraEquivOfFreeOfFinite p O` is
`toCompletedGroupAlgebra`. -/
@[simp]
theorem coe_completedGroupAlgebraEquivOfFreeOfFinite {p : ℕ} [Fact p.Prime]
    {O : Type*} [CommRing O] [TopologicalSpace O] [IsTopologicalRing O] [T2Space O]
    [Algebra ℤ_[p] O] [ContinuousSMul ℤ_[p] O] [Module.Free ℤ_[p] O] [Module.Finite ℤ_[p] O] :
    ⇑(completedGroupAlgebraEquivOfFreeOfFinite (Γ := Γ) p O) = toCompletedGroupAlgebra :=
  funext <| AlgEquiv.ofBijective_apply _ _

/-- Forgetting invertibility of `completedGroupAlgebraEquivOfFreeOfFinite p O` gives
`toCompletedGroupAlgebra`. -/
@[simp]
theorem toAlgHom_completedGroupAlgebraEquivOfFreeOfFinite {p : ℕ} [Fact p.Prime]
    {O : Type*} [CommRing O] [TopologicalSpace O] [IsTopologicalRing O] [T2Space O]
    [Algebra ℤ_[p] O] [ContinuousSMul ℤ_[p] O] [Module.Free ℤ_[p] O] [Module.Finite ℤ_[p] O] :
    (completedGroupAlgebraEquivOfFreeOfFinite (Γ := Γ) p O).toAlgHom = toCompletedGroupAlgebra :=
  AlgEquiv.toAlgHom_ofBijective _ _

/-- `(completedGroupAlgebraEquivOfFreeOfFinite p O).symm` is a left inverse to
`toCompletedGroupAlgebra`. -/
@[simp]
theorem completedGroupAlgebraEquivOfFreeOfFinite_symm_toCompletedGroupAlgebra
    {p : ℕ} [Fact p.Prime]
    {O : Type*} [CommRing O] [TopologicalSpace O] [IsTopologicalRing O] [T2Space O]
    [Algebra ℤ_[p] O] [ContinuousSMul ℤ_[p] O] [Module.Free ℤ_[p] O] [Module.Finite ℤ_[p] O]
    (ν : D(Γ, O)) :
    (completedGroupAlgebraEquivOfFreeOfFinite p O).symm (toCompletedGroupAlgebra ν) = ν :=
  (completedGroupAlgebraEquivOfFreeOfFinite p O).symm_apply_apply ν

/-- `toCompletedGroupAlgebra` is a right inverse to
`(completedGroupAlgebraEquivOfFreeOfFinite p O).symm`. -/
@[simp]
theorem toCompletedGroupAlgebra_completedGroupAlgebraEquivOfFreeOfFinite_symm
    {p : ℕ} [Fact p.Prime]
    {O : Type*} [CommRing O] [TopologicalSpace O] [IsTopologicalRing O] [T2Space O]
    [Algebra ℤ_[p] O] [ContinuousSMul ℤ_[p] O] [Module.Free ℤ_[p] O] [Module.Finite ℤ_[p] O]
    (y : completedGroupAlgebra O Γ) :
    toCompletedGroupAlgebra ((completedGroupAlgebraEquivOfFreeOfFinite p O).symm y) = y :=
  (completedGroupAlgebraEquivOfFreeOfFinite p O).apply_symm_apply y

/-- `(completedGroupAlgebraEquivOfFreeOfFinite p O).symm` sends the group element `γ` in `O[[Γ]]`
to `dirac O γ`. -/
@[simp]
theorem completedGroupAlgebraEquivOfFreeOfFinite_symm_of {p : ℕ} [Fact p.Prime]
    {O : Type*} [CommRing O] [TopologicalSpace O] [IsTopologicalRing O] [T2Space O]
    [Algebra ℤ_[p] O] [ContinuousSMul ℤ_[p] O] [Module.Free ℤ_[p] O] [Module.Finite ℤ_[p] O]
    (γ : Γ) :
    (completedGroupAlgebraEquivOfFreeOfFinite p O).symm (completedGroupAlgebra.of O Γ γ) =
      dirac O γ := by
  rw [← toCompletedGroupAlgebra_dirac,
    completedGroupAlgebraEquivOfFreeOfFinite_symm_toCompletedGroupAlgebra]

/-- `(completedGroupAlgebraEquivOfFreeOfFinite p O).symm` intertwines coefficient extension along
`algebraMap ℤ_[p] O` on `ℤ_p[[Γ]]` with `extendScalars O ∘ completedGroupAlgebraEquiv.symm`. -/
@[simp]
theorem completedGroupAlgebraEquivOfFreeOfFinite_symm_mapRingHom {p : ℕ} [Fact p.Prime]
    {O : Type*} [CommRing O] [TopologicalSpace O] [IsTopologicalRing O] [T2Space O]
    [Algebra ℤ_[p] O] [ContinuousSMul ℤ_[p] O] [Module.Free ℤ_[p] O] [Module.Finite ℤ_[p] O]
    (x : completedGroupAlgebra ℤ_[p] Γ) :
    (completedGroupAlgebraEquivOfFreeOfFinite p O).symm
        (completedGroupAlgebra.mapRingHom Γ (algebraMap ℤ_[p] O) x) =
      extendScalars O (completedGroupAlgebraEquiv.symm x) := by
  apply (completedGroupAlgebraEquivOfFreeOfFinite p O).injective
  simp

/-- In any finite `ℤ_p`-basis `b` of `O`, `(completedGroupAlgebraEquivOfFreeOfFinite p O).symm`
extracts each scalar coordinate in `ℤ_p[[Γ]]`, converts it to an integral measure, and recombines
in `D(Γ, O)`. -/
theorem completedGroupAlgebraEquivOfFreeOfFinite_symm_apply {p : ℕ} [Fact p.Prime]
    {O : Type*} [CommRing O] [TopologicalSpace O] [IsTopologicalRing O] [T2Space O]
    [Algebra ℤ_[p] O] [ContinuousSMul ℤ_[p] O] [Module.Free ℤ_[p] O] [Module.Finite ℤ_[p] O]
    {ι : Type*} [Fintype ι] (b : Module.Basis ι ℤ_[p] O) (y : completedGroupAlgebra O Γ) :
    (completedGroupAlgebraEquivOfFreeOfFinite p O).symm y =
      ∑ i : ι, b i • extendScalars O
        (completedGroupAlgebraEquiv.symm
          (completedGroupAlgebra.mapAddMonoidHom Γ (b.coord i).toAddMonoidHom y)) := by
  apply (completedGroupAlgebraEquivOfFreeOfFinite p O).injective
  rw [AlgEquiv.apply_symm_apply, coe_completedGroupAlgebraEquivOfFreeOfFinite]
  have hsum : ∑ i : ι, b i • extendScalars O
      (completedGroupAlgebraEquiv.symm
        (completedGroupAlgebra.mapAddMonoidHom Γ (b.coord i).toAddMonoidHom y)) =
      baseChangeAlgEquiv O (∑ i : ι, b i ⊗ₜ[ℤ_[p]]
        completedGroupAlgebraEquiv.symm
          (completedGroupAlgebra.mapAddMonoidHom Γ (b.coord i).toAddMonoidHom y)) := by
    simp [map_sum]
  rw [hsum, toCompletedGroupAlgebra_baseChangeAlgEquiv]
  simp only [map_sum, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq,
    toCompletedGroupAlgebra_completedGroupAlgebraEquiv_symm]
  rw [← map_sum, ← completedGroupAlgebra.baseChangeEquiv_symm_apply b y,
    AlgEquiv.apply_symm_apply]

open Topology in
/-- **Weak-topology homeomorphism for finite free normed `ℤ_p`-algebras.** For a profinite group
`Γ` and a normed commutative `ℤ_p`-algebra `O` that is finite and free over `ℤ_p` with continuous
`ℤ_p`-action (`ContinuousSMul ℤ_[p] O`), `toCompletedGroupAlgebra : D(Γ, O) →ₐ[O] O[[Γ]]` is a
homeomorphism from the weak topology on measures to the inverse-limit topology on the completed
group algebra. -/
theorem isHomeomorph_toCompletedGroupAlgebra_weak_of_free_of_finite (p : ℕ) [Fact p.Prime]
    (O : Type*) [NormedCommRing O] [Algebra ℤ_[p] O] [ContinuousSMul ℤ_[p] O]
    [Module.Free ℤ_[p] O] [Module.Finite ℤ_[p] O] :
    @IsHomeomorph _ _ (WeakTopology (X := Γ) (R := O) (E := O)) _
      (toCompletedGroupAlgebra : D(Γ, O) →ₐ[O] completedGroupAlgebra O Γ) := by
  let _ : TopologicalSpace D(Γ, O) := WeakTopology
  let _ : TopologicalSpace D(Γ, ℤ_[p]) := WeakTopology
  let b := Module.Free.chooseBasis ℤ_[p] O
  have hZp_coe : ⇑(completedGroupAlgebraEquiv (Γ := Γ) (p := p)).toEquiv =
      ⇑(toCompletedGroupAlgebra : D(Γ, ℤ_[p]) →ₐ[ℤ_[p]] completedGroupAlgebra ℤ_[p] Γ) :=
    funext fun μ ↦ completedGroupAlgebraEquiv_apply μ
  have hZp_symm : Continuous ⇑(completedGroupAlgebraEquiv (Γ := Γ) (p := p)).symm :=
    ((completedGroupAlgebraEquiv (Γ := Γ) (p := p)).toEquiv.isHomeomorph_iff.mp
      (by rw [hZp_coe]; exact isHomeomorph_toCompletedGroupAlgebra_weak (Γ := Γ) (p := p))).2
  have hsymm_cont :
      Continuous ⇑(completedGroupAlgebraEquivOfFreeOfFinite (Γ := Γ) p O).symm := by
    have hcont_i (i : _) :
        Continuous (fun y : completedGroupAlgebra O Γ ↦
          extendScalars O ((completedGroupAlgebraEquiv (Γ := Γ) (p := p)).symm
            (completedGroupAlgebra.mapAddMonoidHom Γ (b.coord i).toAddMonoidHom y))) :=
      (continuous_extendScalars_weak (X := Γ) (R := ℤ_[p]) (O := O)).comp
        (hZp_symm.comp
          (completedGroupAlgebra.continuous_mapAddMonoidHom
            (b.coord i).continuous_of_finite_of_compactSpace))
    refine continuous_induced_rng.mpr (continuous_pi fun f : C(Γ, O) ↦ ?_)
    simp only [Function.comp_apply]
    have hfun : (fun y : completedGroupAlgebra O Γ ↦
        (completedGroupAlgebraEquivOfFreeOfFinite p O).symm y f) =
        fun y ↦ ∑ i, b i *
          extendScalars O ((completedGroupAlgebraEquiv (Γ := Γ) (p := p)).symm
            (completedGroupAlgebra.mapAddMonoidHom Γ (b.coord i).toAddMonoidHom y)) f := by
      ext y
      rw [← coe_toCLMEquiv, completedGroupAlgebraEquivOfFreeOfFinite_symm_apply b y,
        map_sum, _root_.sum_apply]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      simp [smul_eq_mul]
    rw [hfun]
    exact continuous_finsetSum _ fun i _ ↦
      continuous_const.mul (((continuous_apply f).comp continuous_induced_dom).comp (hcont_i i))
  have hO_coe : ⇑(completedGroupAlgebraEquivOfFreeOfFinite (Γ := Γ) p O).toEquiv =
      ⇑(toCompletedGroupAlgebra : D(Γ, O) →ₐ[O] completedGroupAlgebra O Γ) := by
    rw [AlgEquiv.toEquiv_eq_coe, AlgEquiv.coe_toEquiv, coe_completedGroupAlgebraEquivOfFreeOfFinite]
  rw [← hO_coe]
  exact (completedGroupAlgebraEquivOfFreeOfFinite (Γ := Γ) p O).toEquiv.isHomeomorph_iff.mpr
    ⟨by rw [hO_coe]; exact continuous_toCompletedGroupAlgebra, hsymm_cont⟩

open Topology in
/-- For a profinite group `Γ` and a finite free normed `ℤ_p`-algebra `O` with continuous
`ℤ_p`-action, `D(Γ, O)` is a topological ring for convolution and the weak topology. -/
theorem isTopologicalRing_weak_of_free_of_finite (p : ℕ) [Fact p.Prime]
    (O : Type*) [NormedCommRing O] [Algebra ℤ_[p] O] [ContinuousSMul ℤ_[p] O]
    [Module.Free ℤ_[p] O] [Module.Finite ℤ_[p] O] :
    @IsTopologicalRing D(Γ, O) WeakTopology _ := by
  let _ : TopologicalSpace D(Γ, O) := WeakTopology
  exact (isHomeomorph_toCompletedGroupAlgebra_weak_of_free_of_finite (Γ := Γ) p O)
    |>.isInducing.isTopologicalRing (toCompletedGroupAlgebra (Γ := Γ) (R := O))

/-- **Weak compactness of `O`-valued measures.** For a profinite group `Γ` and a finite free normed
`ℤ_p`-algebra `O` with continuous `ℤ_p`-action, `D(Γ, O)` is compact for the weak topology. -/
theorem compactSpace_weak_of_free_of_finite (p : ℕ) [Fact p.Prime]
    (O : Type*) [NormedCommRing O] [Algebra ℤ_[p] O] [ContinuousSMul ℤ_[p] O]
    [Module.Free ℤ_[p] O] [Module.Finite ℤ_[p] O] :
    @CompactSpace D(Γ, O) (WeakTopology (X := Γ) (R := O) (E := O)) := by
  let _ : TopologicalSpace D(Γ, O) := WeakTopology
  have : CompactSpace O := Module.Finite.compactSpace ℤ_[p] O
  exact ((isHomeomorph_toCompletedGroupAlgebra_weak_of_free_of_finite (Γ := Γ) p O).homeomorph
    _).symm.compactSpace

end ProfinitePadicInt

section Examples

variable {p : ℕ} [Fact p.Prime] [IsTopologicalGroup Γ] [TotallyDisconnectedSpace Γ]
  (O : Type*) [NormedCommRing O] [Algebra ℤ_[p] O] [ContinuousSMul ℤ_[p] O]
  [Module.Free ℤ_[p] O] [Module.Finite ℤ_[p] O]

/-! Sanity check: `completedGroupAlgebraEquivOfFreeOfFinite p O` identifies `a • dirac O γ` with
`a • completedGroupAlgebra.of O Γ γ`. -/

example (a : O) (γ : Γ) :
    completedGroupAlgebraEquivOfFreeOfFinite p O (a • dirac O γ) =
      a • completedGroupAlgebra.of O Γ γ := by
  simp

end Examples

end AbstractMeasure
