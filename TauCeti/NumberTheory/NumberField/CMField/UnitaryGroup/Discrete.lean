/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.CMField.UnitaryGroup.AdelicFrame
import TauCeti.NumberTheory.NumberField.CMField.UnitaryGroup.Compact
import TauCeti.NumberTheory.NumberField.Global.Adeles.Discrete
import TauCeti.Topology.Algebra.Group.Cocompact
import TauCeti.Topology.Algebra.Group.DiscontinuousSubgroup
import TauCeti.Topology.Algebra.Group.Subgroup
import TauCeti.Topology.Algebra.Matrix.GeneralLinearGroup.Basic

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
* When the archimedean group `G_∞(s)` is compact, as for the definite signs `s = (1, …, 1)`
  (`TauCeti.isCompact_infiniteAdelicUnitaryGroup_of_forall_eq`), the projection `G(s) → G_f` is
  proper (`TauCeti.adelicUnitaryGroup.isProperMap_finitePart`). Then the finite rational points
  `Γ_{V,f}`, the image of `Γ_V` in `G_f`, form a discrete subgroup of `G_f` as well: the elements
  of `Γ_V` whose finite component lies in the compact open subgroup `K₀ = G_f ∩ GL_n(Ô)` lie in
  the compact set `G_∞(s) × K₀`, so there are finitely many of them.

The discreteness of `Γ_V` is what makes `Γ_V \ G(s)` a quotient by a discrete group, over which
automorphic forms are integrated; for definite spaces the discreteness of `Γ_{V,f}`, together with
the compactness of the levels `K`, makes the stabilisers `Γ_{V,f} ∩ g K g⁻¹` finite, as the class
sums of algebraic modular forms need.

## Main results

* `TauCeti.FramedHermitianSpace.discreteTopology_rationalPoints`: `Γ_V` is discrete in `G(s)`.
* `TauCeti.FramedHermitianSpace.discreteTopology_finiteRationalPoints`: if `G_∞(s)` is compact,
  for instance for the signs `(1, …, 1)`, then `Γ_{V,f}` is discrete in `G_f`.

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
  -- The conjugate `x g x⁻¹` in `GL_n(E_∞) × GL_n(𝔸_f)`, its adelic matrix, and the entries of
  -- `x g x⁻¹ - 1` as adeles.
  let conj (g : adelicUnitaryGroup E s) : GL ι (InfiniteAdeleRing E) × GL ι 𝔸ᶠ[E] :=
    V.frame * g * V.frame⁻¹
  let M (g : adelicUnitaryGroup E s) : Matrix ι ι 𝔸[E] :=
    ((prodEquivGL ι (InfiniteAdeleRing E) 𝔸ᶠ[E]).symm (conj g) :
      Matrix ι ι (InfiniteAdeleRing E × 𝔸ᶠ[E]))
  let c (i j : ι) (g : adelicUnitaryGroup E s) : 𝔸[E] :=
    M g i j - algebraMap E 𝔸[E] ((1 : Matrix ι ι E) i j)
  have hM : Continuous M := Units.continuous_val.comp (continuous_prodEquivGL_symm.comp
    ((continuous_const.mul continuous_subtypeVal).mul continuous_const))
  have hc (i j : ι) : Continuous (c i j) := (hM.matrix_elem i j).sub continuous_const
  have hconj (γ : unitaryGroupOf V.gram) : conj (V.rationalEmbedding γ) =
      (GeneralLinearGroup.map (algebraMap E (InfiniteAdeleRing E)) γ,
        GeneralLinearGroup.map (algebraMap E 𝔸ᶠ[E]) γ) := by
    simp only [conj, coe_rationalEmbedding]
    refine Prod.ext ?_ ?_ <;> simp only [Prod.fst_mul, Prod.snd_mul, Prod.fst_inv, Prod.snd_inv] <;>
      group
  have hc_rat (i j : ι) (γ : unitaryGroupOf V.gram) :
      c i j (V.rationalEmbedding γ) =
        algebraMap E 𝔸[E] (((γ : GL ι E) : Matrix ι ι E) i j - (1 : Matrix ι ι E) i j) := by
    simp only [c, M, hconj, coe_prodEquivGL_symm_apply, Matrix.of_apply,
      GeneralLinearGroup.map_apply, map_sub]
    congr 1
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

/-- **For definite signs the finite rational points are discrete**: if the archimedean group
`G_∞(s)` is compact, as for the signs `(1, …, 1)`, then `Γ_{V,f}` is a discrete subgroup of `G_f`.
The projection `G(s) → G_f` is then proper, so the elements of the discrete subgroup `Γ_V` with
finite component in the compact open subgroup `K₀` lie in a compact set, and there are finitely
many of them. -/
instance discreteTopology_finiteRationalPoints [CompactSpace (infiniteAdelicUnitaryGroup E s)]
    (V : FramedHermitianSpace E s) : DiscreteTopology V.finiteRationalPoints := by
  have hC := (adelicUnitaryGroup.isProperMap_finitePart s).isCompact_preimage
    (isCompact_integralAdelicUnitaryGroup E ι)
  refine (V.finiteRationalPoints.discreteTopology_iff_finite_inter_of_isCompact
    (isCompact_integralAdelicUnitaryGroup E ι)
    ((isOpen_integralAdelicUnitaryGroup E ι).mem_nhds (one_mem _))).2
    (((V.rationalPoints.finite_preimage_coe_of_isCompact hC).image
      (adelicUnitaryGroup.finitePart E s ∘ (↑))).subset ?_)
  rintro g ⟨hg, hgK⟩
  rw [SetLike.mem_coe, finiteRationalPoints_eq_map] at hg
  obtain ⟨x, hx, rfl⟩ := hg
  exact ⟨⟨x, hx⟩, hgK, rfl⟩

end FramedHermitianSpace

end TauCeti
