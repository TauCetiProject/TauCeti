/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.CMField.UnitaryGroup.AdelicFrame
public import TauCeti.NumberTheory.NumberField.CMField.UnitaryGroup.AdeleMatrix
import TauCeti.NumberTheory.NumberField.Global.Adeles.Discrete
import TauCeti.Topology.Algebra.Group.Subgroup

/-!
# Discreteness of the rational points of the adelic unitary group

Let `E` be a CM field with infinite adeles `E_∞`, finite adeles `𝔸_f` and adeles
`𝔸 = E_∞ × 𝔸_f`, let `s` be a sign vector, and let `G(s) = G_∞(s) × G_f` be the adelic unitary
group, where `G_∞(s) = U(diag s)(E_∞)` and `G_f = U(1_n)(𝔸_f)`. This file proves that the rational
points of a hermitian space with an adelic frame are discrete, which makes quotients by these
rational points meaningful:

* For a space `V = (J, x)` with an adelic frame of signs `s`, the rational points
  `Γ_V = x⁻¹ U(J)(E⁺) x` form a discrete subgroup of `G(s)`. Indeed, `E` is discrete in `𝔸`, so
  the matrices `x g x⁻¹ - 1` with entries in a small neighbourhood of `0` in `𝔸` form a
  neighbourhood of `1` in `G(s)` meeting `Γ_V` only in `1`.
* For the definite signs `s = (1, …, 1)`, the archimedean group `G_∞(1) = U(n)(E_∞)` is compact
  (`TauCeti.isCompact_infiniteAdelicUnitaryGroup_one`). Then the finite rational points
  `Γ_{V,f}`, the image of `Γ_V` in `G_f`, form a discrete subgroup of `G_f` as well: the elements
  of `Γ_V` whose finite component lies in the compact open subgroup `K₀ = G_f ∩ GL_n(Ô)` lie in
  the compact set `G_∞(1) × K₀`, so there are finitely many of them.

The discreteness of `Γ_V` is what makes `Γ_V \ G(s)` a quotient by a discrete group, over which
automorphic forms are integrated; for definite spaces the discreteness of `Γ_{V,f}`, together with
the compactness of the levels `K`, makes the stabilisers `Γ_{V,f} ∩ g K g⁻¹` finite, as the class
sums of algebraic modular forms need.

## Main results

* `TauCeti.FramedHermitianSpace.discreteTopology_rationalPoints`: `Γ_V` is discrete in `G(s)`.
* `TauCeti.FramedHermitianSpace.discreteTopology_finiteRationalPoints`: for the signs
  `(1, …, 1)`, `Γ_{V,f}` is discrete in `G_f`.

## References

* V. Platonov and A. Rapinchuk, *Algebraic Groups and Number Theory*, Academic Press (1994),
  Chapter 5.
* B. H. Gross, *Algebraic modular forms*, Israel J. Math. 113 (1999), 61–93, §§1, 4.

## Attribution

These statements are those of the instance `DiscreteTopology W.Γf` and
`New.Space.discreteTopology_Gamma` in the files `src/Lib/Adelic/Unitary/WeakApproximation.lean`
and `src/Lib/Adelic/Adeles/StrongApproximation.lean` of grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC); the
formalization here is independent of that code.
-/

public section
noncomputable section

open Matrix NumberField Topology
open scoped NumberField.AdeleRing

namespace TauCeti

/-! ### Discreteness of the rational points -/

namespace FramedHermitianSpace

variable {E : Type*} [Field E] [NumberField E] [IsCMField E] {ι : Type*} [Fintype ι]
  [DecidableEq ι] {s : ι → ℤˣ}

/-- As `E` is discrete in `𝔸`, some neighbourhood `N` of `0` in `𝔸` meets `E` only in `0`, and the
`g ∈ G(s)` such that every entry of `x g x⁻¹ - 1` lies in `N` form a neighbourhood of `1` in `G(s)`
whose preimage under the rational embedding is `{1}`. -/
private theorem exists_mem_nhds_one_eq_one_of_rationalEmbedding_mem
    (V : FramedHermitianSpace E s) :
    ∃ W ∈ 𝓝 (1 : adelicUnitaryGroup E s), ∀ γ, V.rationalEmbedding γ ∈ W → γ = 1 := by
  obtain ⟨N, hN, hmem⟩ := GlobalNumberFields.exists_mem_nhds_zero_eq_zero_of_algebraMap_mem E
  -- The entries of `x g x⁻¹`, and of `x g x⁻¹ - 1`, as adeles.
  let p (i j : ι) (g : adelicUnitaryGroup E s) : 𝔸[E] :=
    (((V.frame.1 * (g : GL ι (InfiniteAdeleRing E) × GL ι 𝔸ᶠ[E]).1 * V.frame.1⁻¹ :
        GL ι (InfiniteAdeleRing E)) : Matrix ι ι (InfiniteAdeleRing E)) i j,
      ((V.frame.2 * (g : GL ι (InfiniteAdeleRing E) × GL ι 𝔸ᶠ[E]).2 * V.frame.2⁻¹ :
        GL ι 𝔸ᶠ[E]) : Matrix ι ι 𝔸ᶠ[E]) i j)
  let c (i j : ι) (g : adelicUnitaryGroup E s) : 𝔸[E] :=
    p i j g - algebraMap E 𝔸[E] ((1 : Matrix ι ι E) i j)
  have hc (i j : ι) : Continuous (c i j) := by
    have hinf : Continuous fun g : adelicUnitaryGroup E s ↦
        ((V.frame.1 * (g : GL ι (InfiniteAdeleRing E) × GL ι 𝔸ᶠ[E]).1 * V.frame.1⁻¹ :
          GL ι (InfiniteAdeleRing E)) : Matrix ι ι (InfiniteAdeleRing E)) :=
      Units.continuous_val.comp ((continuous_const.mul
        (continuous_fst.comp continuous_subtypeVal)).mul continuous_const)
    have hf : Continuous fun g : adelicUnitaryGroup E s ↦
        ((V.frame.2 * (g : GL ι (InfiniteAdeleRing E) × GL ι 𝔸ᶠ[E]).2 * V.frame.2⁻¹ :
          GL ι 𝔸ᶠ[E]) : Matrix ι ι 𝔸ᶠ[E]) :=
      Units.continuous_val.comp ((continuous_const.mul
        (continuous_snd.comp continuous_subtypeVal)).mul continuous_const)
    exact ((hinf.matrix_elem i j).prodMk (hf.matrix_elem i j)).sub continuous_const
  have hc_rat (i j : ι) (γ : unitaryGroupOf V.gram) :
      c i j (V.rationalEmbedding γ) =
        algebraMap E 𝔸[E] (((γ : GL ι E) : Matrix ι ι E) i j - (1 : Matrix ι ι E) i j) := by
    have hinf : V.frame.1 *
        (V.rationalEmbedding γ : GL ι (InfiniteAdeleRing E) × GL ι 𝔸ᶠ[E]).1 * V.frame.1⁻¹ =
          GeneralLinearGroup.map (algebraMap E (InfiniteAdeleRing E)) γ := by
      rw [coe_rationalEmbedding]
      group
    have hf : V.frame.2 *
        (V.rationalEmbedding γ : GL ι (InfiniteAdeleRing E) × GL ι 𝔸ᶠ[E]).2 * V.frame.2⁻¹ =
          GeneralLinearGroup.map (algebraMap E 𝔸ᶠ[E]) γ := by
      rw [coe_rationalEmbedding]
      group
    have hp : p i j (V.rationalEmbedding γ) =
        algebraMap E 𝔸[E] (((γ : GL ι E) : Matrix ι ι E) i j) := by
      refine Prod.ext ?_ ?_
      · simp only [p, hinf, GeneralLinearGroup.map_apply, AdeleRing.algebraMap_fst_def]
      · simp only [p, hf, GeneralLinearGroup.map_apply, AdeleRing.algebraMap_snd_def]
    rw [map_sub, ← hp]
  have hW : (⋂ i, ⋂ j, c i j ⁻¹' N) ∈ 𝓝 (1 : adelicUnitaryGroup E s) := by
    refine Filter.iInter_mem.2 fun i ↦ Filter.iInter_mem.2 fun j ↦
      (hc i j).continuousAt.preimage_mem_nhds ?_
    rw [← map_one V.rationalEmbedding, hc_rat]
    simpa using hN
  refine ⟨_, hW, fun γ hγ ↦ unitaryGroupOf.ext (Matrix.ext fun i j ↦ ?_)⟩
  have hγij := Set.mem_iInter₂.1 hγ i j
  rw [Set.mem_preimage, hc_rat] at hγij
  exact sub_eq_zero.1 (hmem _ hγij)

/-- **The rational points of a space with an adelic frame are discrete**: `Γ_V = x⁻¹ U(J)(E⁺) x`
is a discrete subgroup of `G(s)`. As `E` is discrete in `𝔸`, some neighbourhood `N` of `0` in `𝔸`
meets `E` only in `0`, and the `g ∈ G(s)` such that every entry of `x g x⁻¹ - 1` lies in `N` form a
neighbourhood of `1` meeting `Γ_V` only in `1`. -/
instance discreteTopology_rationalPoints (V : FramedHermitianSpace E s) :
    DiscreteTopology V.rationalPoints := by
  obtain ⟨W, hW, hW1⟩ := V.exists_mem_nhds_one_eq_one_of_rationalEmbedding_mem
  rw [rationalPoints_def]
  exact V.rationalEmbedding.discreteTopology_range_of_finite_preimage hW
    ((Set.finite_singleton 1).subset hW1)

/-- **For definite signs the finite rational points are discrete**: if `V` has the signs
`(1, …, 1)`, then `Γ_{V,f}` is a discrete subgroup of `G_f`. The elements of `Γ_V` with finite
component in the compact open subgroup `K₀` lie in the compact set `G_∞(1) × K₀`, and `Γ_V` is
discrete and closed, so there are finitely many of them. -/
instance discreteTopology_finiteRationalPoints (V : FramedHermitianSpace E (1 : ι → ℤˣ)) :
    DiscreteTopology V.finiteRationalPoints := by
  have hC := adelicUnitaryGroup.isCompact_preimage_finitePart
    (isCompact_integralAdelicUnitaryGroup E ι)
  have hΓ : DiscreteTopology (V.rationalPoints : Set (adelicUnitaryGroup E (1 : ι → ℤˣ))) :=
    ((SetLike.isDiscrete_iff_discreteTopology (s := V.rationalPoints)).2 inferInstance).to_subtype
  have hfin : ((V.rationalPoints : Set (adelicUnitaryGroup E (1 : ι → ℤˣ))) ∩
      adelicUnitaryGroup.finitePart E 1 ⁻¹'
        (integralAdelicUnitaryGroup E ι : Set (finiteAdelicUnitaryGroup E ι))).Finite :=
    (hC.inter_left V.rationalPoints.isClosed_of_discreteTopology).finite
      ⟨DiscreteTopology.of_subset hΓ Set.inter_subset_left⟩
  rw [finiteRationalPoints_def]
  refine MonoidHom.discreteTopology_range_of_finite_preimage _
    ((isOpen_integralAdelicUnitaryGroup E ι).mem_nhds (one_mem _))
    ((hfin.preimage V.rationalEmbedding_injective.injOn).subset fun γ hγ ↦
      Set.mem_inter (by rw [SetLike.mem_coe, rationalPoints_def]; exact ⟨γ, rfl⟩) hγ)

end FramedHermitianSpace

end TauCeti
