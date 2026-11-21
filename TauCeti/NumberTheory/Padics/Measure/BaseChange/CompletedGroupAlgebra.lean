/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Measure.BaseChange.Basic
public import TauCeti.NumberTheory.Padics.Measure.CompletedGroupAlgebra
public import TauCeti.Topology.Algebra.Group.Profinite.CompletedGroupAlgebra.BaseChange
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.Topology.Algebra.Module.Compact
import TauCeti.LinearAlgebra.Dual.FiniteProjective
import TauCeti.Topology.Algebra.Ring.Basic
import TauCeti.Topology.ContinuousMap.AutomaticContinuity

/-!
# Finite projective `O`-valued measures and completed group algebras

For a compact, locally compact group `Γ` and a finitely generated projective topological `R`-algebra
`O` carrying the `R`-module topology (`IsModuleTopology R O`), the comparison homomorphism
`AbstractMeasure.toCompletedGroupAlgebra : D(Γ, ·) →ₐ[·] ·[[Γ]]` intertwines scalar retraction
`AbstractMeasure.mapScalars`, scalar extension `AbstractMeasure.extendScalars`, and finite
projective measure base change `AbstractMeasure.baseChangeAlgEquiv` with the corresponding maps
`completedGroupAlgebra.mapAddMonoidHom`, `completedGroupAlgebra.mapRingHom`, and
`completedGroupAlgebra.baseChangeEquiv` on the completed group algebra.

This transfers injectivity, surjectivity, and bijectivity of `toCompletedGroupAlgebra` from `R` to
`O` (`toCompletedGroupAlgebra_injective_of_injective`,
`toCompletedGroupAlgebra_surjective_of_surjective`, `completedGroupAlgebraEquivOfBijective`), and
for normed commutative rings `R` and `O` also transfers the weak-topology homeomorphism
(`isHomeomorph_toCompletedGroupAlgebra_weak_of_isHomeomorph`).

When `Γ` is a profinite group and `R = ℤ_p`, combining this transfer with the integral-measure
isomorphism `AbstractMeasure.completedGroupAlgebraEquiv : D(Γ, ℤ_[p]) ≃ₐ[ℤ_[p]] ℤ_[p][[Γ]]` proves
that `toCompletedGroupAlgebra : D(Γ, O) →ₐ[O] O[[Γ]]` is an isomorphism of `O`-algebras for any
finite projective (in particular, finite free) Hausdorff topological `ℤ_p`-algebra `O` with
continuous `ℤ_p`-action (`AbstractMeasure.completedGroupAlgebraEquivOfFreeOfFinite`,
Rodrigues Jacinto–Williams, Proposition 3.16). When `O` is moreover a normed commutative ring, this
isomorphism is a homeomorphism from the weak topology on `D(Γ, O)` to the inverse-limit topology
on `O[[Γ]]`, making `(D(Γ, O), WeakTopology)` a compact topological ring.

## Main definitions

* `AbstractMeasure.completedGroupAlgebraEquivOfBijective O hb`: the `O`-algebra isomorphism
  `D(Γ, O) ≃ₐ[O] completedGroupAlgebra O Γ` transferred from bijectivity of
  `toCompletedGroupAlgebra` over `R`.
* `AbstractMeasure.completedGroupAlgebraEquivOfFreeOfFinite p O`: the `O`-algebra isomorphism
  `D(Γ, O) ≃ₐ[O] completedGroupAlgebra O Γ` for a profinite group `Γ` and a finite free Hausdorff
  topological `ℤ_p`-algebra `O` with continuous `ℤ_p`-action (`ContinuousSMul ℤ_[p] O`).

## Main results

* `AbstractMeasure.toCompletedGroupAlgebra_mapScalars`,
  `AbstractMeasure.toCompletedGroupAlgebra_extendScalars`,
  `AbstractMeasure.toCompletedGroupAlgebra_baseChangeAlgEquiv`: compatibility of
  `toCompletedGroupAlgebra` with scalar retraction, scalar extension, and finite projective base
  change.
* `AbstractMeasure.toCompletedGroupAlgebra_injective_of_injective`,
  `AbstractMeasure.toCompletedGroupAlgebra_surjective_of_surjective`,
  `AbstractMeasure.isHomeomorph_toCompletedGroupAlgebra_weak_of_isHomeomorph`: general transfer of
  injectivity, surjectivity, and the weak-topology homeomorphism along finite projective
  `IsModuleTopology` extensions.
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

open ContinuousMap TauCeti Topology
open scoped TensorProduct

namespace AbstractMeasure

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [CompactSpace Γ]

section CompactGroup

variable {R O : Type*} [ContinuousMul Γ] [LocallyCompactSpace Γ]
  [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [CommRing O] [TopologicalSpace O] [IsTopologicalRing O]
  [Algebra R O] [IsModuleTopology R O] [Module.Projective R O] [Module.Finite R O]

local instance : ContinuousSMul R O := IsModuleTopology.toContinuousSMul R O

omit [Module.Projective R O] [Module.Finite R O] in
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

/-- If `toCompletedGroupAlgebra : D(Γ, R) →ₐ[R] R[[Γ]]` is injective, then so is
`toCompletedGroupAlgebra : D(Γ, O) →ₐ[O] O[[Γ]]` for any finite projective `R`-algebra `O` carrying
the `R`-module topology. -/
theorem toCompletedGroupAlgebra_injective_of_injective
    (hi : Function.Injective
      (toCompletedGroupAlgebra : D(Γ, R) →ₐ[R] completedGroupAlgebra R Γ)) :
    Function.Injective
      (toCompletedGroupAlgebra : D(Γ, O) →ₐ[O] completedGroupAlgebra O Γ) := by
  obtain ⟨n, b, φ, hsum⟩ := TauCeti.exists_sum_dual_smul_eq (R := R) (M := O)
  intro ν₁ ν₂ h
  refine ext_of_apply_comp_algebraMap R fun g ↦ ?_
  have hφ (i : Fin n) : mapScalars (φ i) ν₁ = mapScalars (φ i) ν₂ :=
    hi <| by rw [toCompletedGroupAlgebra_mapScalars, toCompletedGroupAlgebra_mapScalars, h]
  rw [← hsum (ν₁ _), ← hsum (ν₂ _)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← mapScalars_apply, ← mapScalars_apply, hφ i]

/-- If `toCompletedGroupAlgebra : D(Γ, R) →ₐ[R] R[[Γ]]` is surjective, then so is
`toCompletedGroupAlgebra : D(Γ, O) →ₐ[O] O[[Γ]]` for any finite projective `R`-algebra `O` carrying
the `R`-module topology. -/
theorem toCompletedGroupAlgebra_surjective_of_surjective
    (hs : Function.Surjective
      (toCompletedGroupAlgebra : D(Γ, R) →ₐ[R] completedGroupAlgebra R Γ)) :
    Function.Surjective
      (toCompletedGroupAlgebra : D(Γ, O) →ₐ[O] completedGroupAlgebra O Γ) := by
  intro y
  obtain ⟨z, hz⟩ := Algebra.TensorProduct.map_surjective (AlgHom.id O O)
    (toCompletedGroupAlgebra : D(Γ, R) →ₐ[R] completedGroupAlgebra R Γ) Function.surjective_id hs
    ((completedGroupAlgebra.baseChangeEquiv R O Γ).symm y)
  refine ⟨baseChangeAlgEquiv O z, ?_⟩
  rw [toCompletedGroupAlgebra_baseChangeAlgEquiv, hz, AlgEquiv.apply_symm_apply]

variable (O) in
/-- If `toCompletedGroupAlgebra : D(Γ, R) →ₐ[R] R[[Γ]]` is bijective, then
`toCompletedGroupAlgebra : D(Γ, O) →ₐ[O] O[[Γ]]` is an `O`-algebra isomorphism. -/
def completedGroupAlgebraEquivOfBijective
    (hb : Function.Bijective
      (toCompletedGroupAlgebra : D(Γ, R) →ₐ[R] completedGroupAlgebra R Γ)) :
    D(Γ, O) ≃ₐ[O] completedGroupAlgebra O Γ :=
  AlgEquiv.ofBijective toCompletedGroupAlgebra
    ⟨toCompletedGroupAlgebra_injective_of_injective hb.1,
      toCompletedGroupAlgebra_surjective_of_surjective hb.2⟩

@[simp]
theorem coe_completedGroupAlgebraEquivOfBijective
    (hb : Function.Bijective
      (toCompletedGroupAlgebra : D(Γ, R) →ₐ[R] completedGroupAlgebra R Γ)) :
    ⇑(completedGroupAlgebraEquivOfBijective O hb) =
      (toCompletedGroupAlgebra : D(Γ, O) →ₐ[O] completedGroupAlgebra O Γ) :=
  (rfl)

@[simp]
theorem toAlgHom_completedGroupAlgebraEquivOfBijective
    (hb : Function.Bijective
      (toCompletedGroupAlgebra : D(Γ, R) →ₐ[R] completedGroupAlgebra R Γ)) :
    (completedGroupAlgebraEquivOfBijective O hb).toAlgHom = toCompletedGroupAlgebra :=
  (rfl)

@[simp]
theorem completedGroupAlgebraEquivOfBijective_symm_toCompletedGroupAlgebra
    (hb : Function.Bijective
      (toCompletedGroupAlgebra : D(Γ, R) →ₐ[R] completedGroupAlgebra R Γ))
    (ν : D(Γ, O)) :
    (completedGroupAlgebraEquivOfBijective O hb).symm (toCompletedGroupAlgebra ν) = ν := by
  apply (completedGroupAlgebraEquivOfBijective O hb).injective
  simp

@[simp]
theorem completedGroupAlgebraEquivOfBijective_symm_of
    (hb : Function.Bijective
      (toCompletedGroupAlgebra : D(Γ, R) →ₐ[R] completedGroupAlgebra R Γ))
    (γ : Γ) :
    (completedGroupAlgebraEquivOfBijective O hb).symm (completedGroupAlgebra.of O Γ γ) =
      dirac O γ := by
  rw [← toCompletedGroupAlgebra_dirac,
    completedGroupAlgebraEquivOfBijective_symm_toCompletedGroupAlgebra]

omit [Module.Projective R O] [Module.Finite R O] in
private theorem apply_eq_sum_of_dual_of_leftInverse
    {n : ℕ} {b : Fin n → O} {φ : Fin n → Module.Dual R O}
    (hsum : ∀ a : O, ∑ i, φ i a • b i = a)
    (inv : completedGroupAlgebra R Γ → D(Γ, R))
    (hinv : Function.LeftInverse inv toCompletedGroupAlgebra)
    (f : C(Γ, O)) (ν : D(Γ, O)) :
    ν f = ∑ j : Fin n, b j *
      ∑ i : Fin n,
        (inv (completedGroupAlgebra.mapAddMonoidHom Γ
          (φ i).toAddMonoidHom (toCompletedGroupAlgebra ν))
            ((⟨φ j, IsModuleTopology.continuous_of_linearMap (φ j)⟩ : C(O, R)).comp f)) • b i := by
  conv_lhs => rw [ContinuousMap.eq_sum_smul_algebraMapCLM_comp_of_dual hsum f]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [map_smul, smul_eq_mul]
  congr 1
  conv_lhs =>
    rw [← hsum (ν ((algebraMapCLM R O : C(R, O)).comp
      ((⟨φ j, IsModuleTopology.continuous_of_linearMap (φ j)⟩ : C(O, R)).comp f)))]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  congr 1
  rw [← mapScalars_apply (φ i), ← toCompletedGroupAlgebra_mapScalars, hinv _]

end CompactGroup

section Normed

variable [ContinuousMul Γ] [LocallyCompactSpace Γ]

/-- For normed commutative rings `R` and `O` where `O` is a finitely generated projective
`R`-algebra carrying the `R`-module topology, if `toCompletedGroupAlgebra : D(Γ, R) →ₐ[R] R[[Γ]]`
is a homeomorphism from the weak topology to the inverse-limit topology, then so is
`toCompletedGroupAlgebra : D(Γ, O) →ₐ[O] O[[Γ]]`. -/
theorem isHomeomorph_toCompletedGroupAlgebra_weak_of_isHomeomorph
    {R O : Type*} [NormedCommRing R] [NormedCommRing O] [Algebra R O]
    [IsModuleTopology R O] [Module.Projective R O] [Module.Finite R O]
    (hh : @IsHomeomorph _ _ (WeakTopology (X := Γ) (R := R) (E := R)) _
      (toCompletedGroupAlgebra : D(Γ, R) →ₐ[R] completedGroupAlgebra R Γ)) :
    @IsHomeomorph _ _ (WeakTopology (X := Γ) (R := O) (E := O)) _
      (toCompletedGroupAlgebra : D(Γ, O) →ₐ[O] completedGroupAlgebra O Γ) := by
  have := IsModuleTopology.toContinuousSMul R O
  obtain ⟨n, b, φ, hsum⟩ := TauCeti.exists_sum_dual_smul_eq (R := R) (M := O)
  let tDR : TopologicalSpace D(Γ, R) := WeakTopology (X := Γ) (R := R) (E := R)
  let eR : completedGroupAlgebra R Γ ≃ₜ D(Γ, R) :=
    (@IsHomeomorph.homeomorph _ _ tDR _ _ hh).symm
  have heR : Function.LeftInverse eR toCompletedGroupAlgebra :=
    (@IsHomeomorph.homeomorph _ _ tDR _ _ hh).left_inv
  have heval (f : C(Γ, O)) :
      Continuous[.induced toCompletedGroupAlgebra inferInstance, _]
        fun ν : D(Γ, O) ↦ ν f := by
    let : TopologicalSpace D(Γ, O) := .induced toCompletedGroupAlgebra inferInstance
    simp_rw [apply_eq_sum_of_dual_of_leftInverse hsum eR heR f]
    refine continuous_finsetSum _ fun j _ ↦ continuous_const.mul <|
      continuous_finsetSum _ fun i _ ↦ ?_
    have hmap : Continuous fun ν : D(Γ, O) ↦
        eR (completedGroupAlgebra.mapAddMonoidHom Γ
          (φ i).toAddMonoidHom (toCompletedGroupAlgebra ν)) :=
      eR.continuous.comp <|
        (completedGroupAlgebra.continuous_mapAddMonoidHom
          (IsModuleTopology.continuous_of_linearMap (φ i))).comp continuous_induced_dom
    let cf : C(Γ, R) :=
      (⟨φ j, IsModuleTopology.continuous_of_linearMap (φ j)⟩ : C(O, R)).comp f
    have hevR : @Continuous D(Γ, R) R tDR _ (fun μ : D(Γ, R) ↦ μ cf) :=
      (continuous_apply cf).comp continuous_induced_dom
    exact (hevR.comp hmap).smul continuous_const
  have hle : .induced toCompletedGroupAlgebra inferInstance ≤
      WeakTopology (X := Γ) (R := O) (E := O) := by
    let : TopologicalSpace D(Γ, O) := .induced toCompletedGroupAlgebra inferInstance
    exact continuous_iff_le_induced.mp (continuous_pi heval)
  let : TopologicalSpace D(Γ, O) := WeakTopology (X := Γ) (R := O) (E := O)
  have hind : IsInducing
      (toCompletedGroupAlgebra : D(Γ, O) →ₐ[O] completedGroupAlgebra O Γ) :=
    ⟨le_antisymm (continuous_iff_le_induced.mp continuous_toCompletedGroupAlgebra) hle⟩
  have hbij := (completedGroupAlgebraEquivOfBijective O hh.bijective).bijective
  exact isHomeomorph_iff_isEmbedding_surjective.mpr ⟨⟨hind, hbij.1⟩, hbij.2⟩

end Normed

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
  have := TauCeti.isModuleTopology_of_finite_of_compactSpace (R := ℤ_[p]) (M := O)
  exact toCompletedGroupAlgebra_surjective_of_surjective
    (toCompletedGroupAlgebra_surjective (p := p))

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
    [Algebra ℤ_[p] O] [ContinuousSMul ℤ_[p] O]
    [Module.Free ℤ_[p] O] [Module.Finite ℤ_[p] O]
    (x : completedGroupAlgebra ℤ_[p] Γ) :
    let := TauCeti.isModuleTopology_of_finite_of_compactSpace (R := ℤ_[p]) (M := O)
    (completedGroupAlgebraEquivOfFreeOfFinite p O).symm
        (completedGroupAlgebra.mapRingHom Γ (algebraMap ℤ_[p] O) x) =
      extendScalars O (completedGroupAlgebraEquiv.symm x) := by
  let := TauCeti.isModuleTopology_of_finite_of_compactSpace (R := ℤ_[p]) (M := O)
  apply (completedGroupAlgebraEquivOfFreeOfFinite p O).injective
  simp

/-- In any finite `ℤ_p`-basis `b` of `O`, `(completedGroupAlgebraEquivOfFreeOfFinite p O).symm`
extracts each scalar coordinate in `ℤ_p[[Γ]]`, converts it to an integral measure, and recombines
in `D(Γ, O)`. -/
theorem completedGroupAlgebraEquivOfFreeOfFinite_symm_apply {p : ℕ} [Fact p.Prime]
    {O : Type*} [CommRing O] [TopologicalSpace O] [IsTopologicalRing O] [T2Space O]
    [Algebra ℤ_[p] O] [ContinuousSMul ℤ_[p] O]
    [Module.Free ℤ_[p] O] [Module.Finite ℤ_[p] O]
    {ι : Type*} [Fintype ι] (b : Module.Basis ι ℤ_[p] O) (y : completedGroupAlgebra O Γ) :
    let := TauCeti.isModuleTopology_of_finite_of_compactSpace (R := ℤ_[p]) (M := O)
    (completedGroupAlgebraEquivOfFreeOfFinite p O).symm y =
      ∑ i : ι, b i • extendScalars O
        (completedGroupAlgebraEquiv.symm
          (completedGroupAlgebra.mapAddMonoidHom Γ (b.coord i).toAddMonoidHom y)) := by
  let := TauCeti.isModuleTopology_of_finite_of_compactSpace (R := ℤ_[p]) (M := O)
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
  have := TauCeti.isModuleTopology_of_finite_of_compactSpace (R := ℤ_[p]) (M := O)
  exact isHomeomorph_toCompletedGroupAlgebra_weak_of_isHomeomorph
    (isHomeomorph_toCompletedGroupAlgebra_weak (Γ := Γ) (p := p))

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
