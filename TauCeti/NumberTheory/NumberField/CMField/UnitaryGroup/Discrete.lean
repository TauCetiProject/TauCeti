/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.CMField.UnitaryGroup.AdelicFrame
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Normed.Field.ProperSpace
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.MetricSpace.Isometry
import TauCeti.NumberTheory.NumberField.Global.Adeles.Discrete
import TauCeti.Topology.Algebra.Group.Subgroup

/-!
# The adelic unitary group in the adelic matrices, and discreteness of rational points

Let `E` be a CM field with infinite adeles `E_∞`, finite adeles `𝔸_f` and adeles
`𝔸 = E_∞ × 𝔸_f`, let `s` be a sign vector, and let `G(s) = G_∞(s) × G_f` be the adelic unitary
group, where `G_∞(s) = U(diag s)(E_∞)` and `G_f = U(1_n)(𝔸_f)`. This file proves the topological
facts about `G(s)` and the rational points of a hermitian space with an adelic frame that make
quotients by these rational points meaningful:

* `g ↦` (the adelic matrix of `g`) is a closed embedding of `G(s)` in `M_n(𝔸)`. This identifies
  the topology of `G(s)`, which is that of the pairs `(g, g⁻¹)` in `GL_n(E_∞) × GL_n(𝔸_f)`, with
  the subspace topology of the matrices: the inverse of an element of a unitary group is a
  continuous function of the element.
* For a space `V = (J, x)` with an adelic frame of signs `s`, the rational points
  `Γ_V = x⁻¹ U(J)(E⁺) x` form a discrete subgroup of `G(s)`. Indeed, `E` is discrete in `𝔸`, so
  the matrices `x g x⁻¹ - 1` with entries in a small neighbourhood of `0` in `𝔸` form a
  neighbourhood of `1` in `G(s)` meeting `Γ_V` only in `1`.
* For the definite signs `s = (1, …, 1)`, the archimedean group `G_∞(1) = U(n)(E_∞)` is compact,
  as the entries of a unitary matrix have absolute value at most one at every infinite place.
  Then the finite rational points `Γ_{V,f}`, the image of `Γ_V` in `G_f`, form a discrete subgroup
  of `G_f` as well: the elements of `Γ_V` whose finite component lies in the compact open subgroup
  `K₀ = G_f ∩ GL_n(Ô)` lie in the compact set `G_∞(1) × K₀`, so there are finitely many of them.

The discreteness of `Γ_V` is what makes `Γ_V \ G(s)` a quotient by a discrete group, over which
automorphic forms are integrated; for definite spaces the discreteness of `Γ_{V,f}`, together with
the compactness of the levels `K`, makes the stabilisers `Γ_{V,f} ∩ g K g⁻¹` finite, as the class
sums of algebraic modular forms need.

## Main definitions

* `TauCeti.adelicUnitaryGroup.toAdeleMatrix E s`: the adelic matrix `G(s) →* M_n(𝔸)`.

## Main results

* `TauCeti.adelicUnitaryGroup.isClosedEmbedding_toAdeleMatrix`: the adelic matrix is a closed
  embedding.
* `TauCeti.norm_apply_le_one_of_star_mul_self_eq_one`: the entries of a unitary matrix over the
  infinite adeles have norm at most one at every infinite place, and
  `TauCeti.isCompact_infiniteAdelicUnitaryGroup_one`: `G_∞(1)` is compact, so that
  `TauCeti.adelicUnitaryGroup.isCompact_preimage_finitePart`: compact subsets of `G_f` have compact
  preimages in `G(1)`.
* `TauCeti.FramedHermitianSpace.discreteTopology_rationalPoints`: `Γ_V` is discrete in `G(s)`.
* `TauCeti.FramedHermitianSpace.discreteTopology_finiteRationalPoints`: for the signs
  `(1, …, 1)`, `Γ_{V,f}` is discrete in `G_f`.

## References

* V. Platonov and A. Rapinchuk, *Algebraic Groups and Number Theory*, Academic Press (1994),
  Chapter 5.
* B. H. Gross, *Algebraic modular forms*, Israel J. Math. 113 (1999), 61–93, §§1, 4.

## Attribution

These statements are those of `New.G.isClosedEmbedding_adeleMatrix`, the instance
`DiscreteTopology W.Γf` and `New.Space.discreteTopology_Gamma` in the files
`src/Lib/Adelic/Unitary/WeakApproximation.lean` and `src/Lib/Adelic/Adeles/StrongApproximation.lean`
of grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC); the
formalization here is independent of that code.
-/

public section
noncomputable section

open Matrix NumberField Topology
open scoped NumberField.AdeleRing

namespace TauCeti

/-! ### The archimedean unitary group of the definite form is compact -/

section Compact

variable {E : Type*} [Field E] [CharZero E] [Algebra.IsIntegral ℚ E] [IsCMField E] {ι : Type*}
  [Fintype ι] [DecidableEq ι]

/-- **The entries of a unitary matrix over the infinite adeles have norm at most one.** If
`M* M = 1` for a square matrix `M` over the infinite adeles of a CM field, then every entry of `M`
has norm at most one at every infinite place `w`: read in `ℂ` through the embedding attached to
`w`, which turns conjugation into complex conjugation, `M` becomes a unitary complex matrix
(`entry_norm_bound_of_unitary`). -/
theorem norm_apply_le_one_of_star_mul_self_eq_one {M : Matrix ι ι (InfiniteAdeleRing E)}
    (hM : star M * M = 1) (i j : ι) (w : InfinitePlace E) : ‖M i j w‖ ≤ 1 := by
  -- Evaluation at `w` followed by the embedding `E_w → ℂ`, as a ring homomorphism.
  let ψ : InfiniteAdeleRing E →+* ℂ :=
    (InfinitePlace.Completion.extensionEmbedding w).comp (Pi.evalRingHom _ w)
  have hψ : Function.Semiconj ψ star star := fun a ↦
    InfiniteAdeleRing.extensionEmbedding_star_apply a w
  have hU : M.map ψ ∈ unitaryGroup ι ℂ := by
    rw [mem_unitaryGroup_iff']
    calc star (M.map ψ) * M.map ψ = (star M * M).map ψ := by
          rw [star_eq_conjTranspose, star_eq_conjTranspose, ← conjTranspose_map ψ hψ,
            Matrix.map_mul]
      _ = 1 := by rw [hM, Matrix.map_one ψ (map_zero ψ) (map_one ψ)]
  calc ‖M i j w‖ = ‖M.map ψ i j‖ :=
        ((InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero
          (map_zero _) (M i j w)).symm
    _ ≤ 1 := entry_norm_bound_of_unitary hU i j

variable (E ι) in
/-- **The archimedean unitary group of the definite form is compact**: `G_∞(1) = U(n)(E_∞)` is a
closed subset of the matrices over the infinite adeles, whose entries have norm at most one at
every infinite place (`norm_apply_le_one_of_star_mul_self_eq_one`). -/
theorem isCompact_infiniteAdelicUnitaryGroup_one :
    IsCompact (infiniteAdelicUnitaryGroup E (1 : ι → ℤˣ) : Set (GL ι (InfiniteAdeleRing E))) := by
  have hball (w : InfinitePlace E) : IsCompact (Metric.closedBall (0 : w.Completion) 1) :=
    haveI := ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace w.Completion
    isCompact_closedBall 0 1
  have hd : (diagonal fun i ↦ (((1 : ι → ℤˣ) i : ℤ) : InfiniteAdeleRing E)) = 1 := by simp
  have he := unitaryGroupOf.isClosedEmbedding_val
    (A := diagonal fun i ↦ (((1 : ι → ℤˣ) i : ℤ) : InfiniteAdeleRing E)) (hd ▸ isUnit_one)
  have hB : IsCompact (Set.matrix (m := ι) (n := ι) (Set.univ.pi fun w : InfinitePlace E ↦
      Metric.closedBall (0 : w.Completion) 1 : Set (InfiniteAdeleRing E))) :=
    (isCompact_univ_pi hball).matrix
  refine isCompact_iff_compactSpace.2 (isCompact_univ_iff.1 ?_)
  convert he.isCompact_preimage hB using 1
  refine (Set.eq_univ_of_forall fun g ↦ ?_).symm
  have hg : star ((g : GL ι (InfiniteAdeleRing E)) : Matrix ι ι (InfiniteAdeleRing E)) *
      ((g : GL ι (InfiniteAdeleRing E)) : Matrix ι ι (InfiniteAdeleRing E)) = 1 := by
    simpa [hd] using mem_unitaryGroupOf_iff.1 g.property
  rw [Set.mem_preimage, Set.mem_matrix]
  intro i j w _
  rw [Metric.mem_closedBall, dist_zero_right]
  exact norm_apply_le_one_of_star_mul_self_eq_one hg i j w

instance : CompactSpace (infiniteAdelicUnitaryGroup E (1 : ι → ℤˣ)) :=
  isCompact_iff_compactSpace.mp (isCompact_infiniteAdelicUnitaryGroup_one E ι)

end Compact

/-! ### The adelic matrix -/

section AdeleMatrix

variable (E : Type*) [Field E] [NumberField E] [IsCMField E] {ι : Type*} [Fintype ι]
  [DecidableEq ι]

/-- The **adelic matrix** of an element `g = (g_∞, g_f)` of the adelic unitary group `G(s)`: the
matrix in `M_n(𝔸)`, `𝔸 = E_∞ × 𝔸_f`, whose entry `(i, j)` is the adele `(g_∞ i j, g_f i j)`. It
is multiplicative, and a closed embedding (`isClosedEmbedding_toAdeleMatrix`). -/
def adelicUnitaryGroup.toAdeleMatrix (s : ι → ℤˣ) : adelicUnitaryGroup E s →* Matrix ι ι 𝔸[E] :=
  ((Matrix.prodRingEquiv ι (InfiniteAdeleRing E) 𝔸ᶠ[E]).symm.toMonoidHom.comp
    ((Units.coeHom _).prodMap (Units.coeHom _))).comp (adelicUnitaryGroup E s).subtype

variable {E}

/-- The archimedean component of the entry `(i, j)` of the adelic matrix of `g` is `g_∞ i j`. -/
@[simp]
theorem adelicUnitaryGroup.fst_toAdeleMatrix_apply {s : ι → ℤˣ} (g : adelicUnitaryGroup E s)
    (i j : ι) :
    (adelicUnitaryGroup.toAdeleMatrix E s g i j).1 =
      ((g : GL ι (InfiniteAdeleRing E) × GL ι 𝔸ᶠ[E]).1 : Matrix ι ι (InfiniteAdeleRing E)) i j :=
  (rfl)

/-- The finite component of the entry `(i, j)` of the adelic matrix of `g` is `g_f i j`. -/
@[simp]
theorem adelicUnitaryGroup.snd_toAdeleMatrix_apply {s : ι → ℤˣ} (g : adelicUnitaryGroup E s)
    (i j : ι) :
    (adelicUnitaryGroup.toAdeleMatrix E s g i j).2 =
      ((g : GL ι (InfiniteAdeleRing E) × GL ι 𝔸ᶠ[E]).2 : Matrix ι ι 𝔸ᶠ[E]) i j :=
  (rfl)

/-- **`G(s)` is a closed subset of the adelic matrices**: the adelic matrix
`G(s) → M_n(𝔸)` is a closed embedding. The unitary groups `G_∞(s)` and `G_f` are closed subsets
of the matrices over `E_∞` and over `𝔸_f` with the subspace topology
(`Matrix.unitaryGroupOf.isClosedEmbedding_val`), and `M_n(𝔸)` is `M_n(E_∞) × M_n(𝔸_f)`. -/
theorem adelicUnitaryGroup.isClosedEmbedding_toAdeleMatrix (s : ι → ℤˣ) :
    IsClosedEmbedding (adelicUnitaryGroup.toAdeleMatrix E s) := by
  have hs : IsUnit (diagonal fun i ↦ ((s i : ℤ) : InfiniteAdeleRing E)) :=
    isUnit_diagonal.2 (Pi.isUnit_iff.2 fun i ↦ (s i).isUnit.map (Int.castRingHom _))
  have hf := unitaryGroupOf.isClosedEmbedding_val (A := (1 : Matrix ι ι 𝔸ᶠ[E])) isUnit_one
  rw [unitaryGroupOf_one] at hf
  -- `M_n(E_∞ × 𝔸_f)` is homeomorphic to `M_n(E_∞) × M_n(𝔸_f)`.
  let e : Matrix ι ι 𝔸[E] ≃ₜ Matrix ι ι (InfiniteAdeleRing E) × Matrix ι ι 𝔸ᶠ[E] :=
    { Matrix.prodEquiv ι ι (InfiniteAdeleRing E) 𝔸ᶠ[E] with
      continuous_toFun := (continuous_id.matrix_map continuous_fst).prodMk
        (continuous_id.matrix_map continuous_snd)
      continuous_invFun := continuous_pi fun i ↦ continuous_pi fun j ↦
        ((continuous_apply j).comp ((continuous_apply i).comp continuous_fst)).prodMk
          ((continuous_apply j).comp ((continuous_apply i).comp continuous_snd)) }
  exact e.symm.isClosedEmbedding.comp
    (((unitaryGroupOf.isClosedEmbedding_val hs).prodMap hf).comp
      (Homeomorph.Set.prod _ _).isClosedEmbedding)

/-- The adelic matrix `G(s) → M_n(𝔸)` is continuous. -/
@[fun_prop]
theorem adelicUnitaryGroup.continuous_toAdeleMatrix (s : ι → ℤˣ) :
    Continuous (adelicUnitaryGroup.toAdeleMatrix E s) :=
  (adelicUnitaryGroup.isClosedEmbedding_toAdeleMatrix s).continuous

/-- **For definite signs, compact sets have compact preimages in `G(1)`**: the preimage in
`G(1) = G_∞(1) × G_f` of a compact subset `S` of `G_f` is `G_∞(1) × S`, which is compact as
`G_∞(1)` is (`isCompact_infiniteAdelicUnitaryGroup_one`). -/
theorem adelicUnitaryGroup.isCompact_preimage_finitePart {S : Set (finiteAdelicUnitaryGroup E ι)}
    (hS : IsCompact S) : IsCompact (adelicUnitaryGroup.finitePart E (1 : ι → ℤˣ) ⁻¹' S) := by
  -- The pair map `G_∞(1) × G_f → G(1)` carries `G_∞(1) × S` onto the preimage of `S`.
  let ψ : infiniteAdelicUnitaryGroup E (1 : ι → ℤˣ) × finiteAdelicUnitaryGroup E ι →
      adelicUnitaryGroup E (1 : ι → ℤˣ) := fun p ↦ ⟨(p.1, p.2), p.1.property, p.2.property⟩
  have hψ : Continuous ψ := (continuous_subtypeVal.prodMap continuous_subtypeVal).subtype_mk _
  have hfin (p) : adelicUnitaryGroup.finitePart E 1 (ψ p) = p.2 :=
    Subtype.ext (adelicUnitaryGroup.coe_finitePart _)
  convert (isCompact_univ.prod hS).image hψ using 1
  ext g
  refine ⟨fun hg ↦ ⟨(⟨_, g.property.1⟩, adelicUnitaryGroup.finitePart E 1 g), ⟨trivial, hg⟩,
    Subtype.ext (Prod.ext rfl (adelicUnitaryGroup.coe_finitePart g))⟩, ?_⟩
  rintro ⟨p, ⟨-, hp⟩, rfl⟩
  rwa [Set.mem_preimage, hfin]

end AdeleMatrix

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
