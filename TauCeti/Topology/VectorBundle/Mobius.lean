/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import TauCeti.AlgebraicTopology.Singular.AddCircle
public import TauCeti.Topology.VectorBundle.IdempotentRange
public import TauCeti.Topology.VectorBundle.SphereBundle
import Mathlib.Data.ZMod.QuotientGroup
import TauCeti.AlgebraicTopology.Singular.Reduced
import TauCeti.Topology.VectorBundle.Smul

/-!
# The Möbius line bundle and the relative homology of its Thom pair

The **Möbius line bundle** over the circle `AddCircle p` has as fibre over `θ` the real line
`ℝ u ⊆ ℂ`, where `u² = z = toCircle θ` (`TauCeti.MobiusLine`). It is the range of the real
projection `w ↦ (w + z * conj w) / 2` (`TauCeti.mobiusProjection`), so it is the image bundle of a
continuous family of projections of the trivial bundle with fibre `ℂ`, and a topological vector
bundle with model fibre `ℝ` (`TauCeti.rangeFiberBundle`, `TauCeti.rangeVectorBundle`). Going once
around the circle turns `u` through half a turn, so each fibre comes back with its orientation
reversed. Its unit vectors
`u` lie over `u²`: the unit circle bundle is a circle, and the projection restricted to it is the
double cover `θ ↦ 2 • θ` (`TauCeti.mobiusSphereHomeomorph`).

The Thom pair `(E, E₀)` of the bundle is its total space relative to the nonzero vectors
(`TauCeti.thomPair`). The total space retracts onto the circle and the nonzero vectors retract onto
the unit circle bundle, so in the long exact sequence of the pair the inclusion `E₀ ⊆ E` is the
double cover. It induces multiplication by `2` on `H₁(S¹; ℤ) ≃ ℤ` and an isomorphism on `H₀`, hence

`H₁(E, E₀; ℤ) ≃ ℤ/2`

(`TauCeti.nonempty_linearEquiv_singularHomology_thomPair_mobiusLine_one`). In particular this group
is not the zeroth homology `H₀(S¹; ℤ) ≃ ℤ` of the base
(`TauCeti.not_nonempty_linearEquiv_singularHomology_thomPair_mobiusLine_one_zero`). The Thom
isomorphism `H_{j+1}(E, E₀; ℤ) ≃ H_j(S¹; ℤ)` with constant integer coefficients, which holds for
an orientable line bundle, therefore fails for the Möbius line already in degree `j = 0`. The
group `ℤ/2` is instead the zeroth homology of the circle with coefficients in the orientation
local system of the bundle, the coinvariants of `ℤ` under the loop acting by `-1`; that twisted
Thom isomorphism is not proved here. This is the situation of a Morse–Bott function whose negative
normal bundle along a critical circle is the Möbius line: attaching the negative disc bundle
across the critical level identifies the relative integral homology of the critical band with that
of this Thom pair, which is `ℤ/2` in degree `1` and not `ℤ`.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §9 and §10 (the Thom isomorphism and its orientation hypothesis).
* R. L. Cohen, K. Iga, P. Norbury, *Topics in Morse Theory*, lecture notes, Theorem 15.4
  (the Morse–Bott attachment and its orientation coefficients).
-/

public section

open Bundle Complex CategoryTheory
open scoped ComplexConjugate ContinuousMap

namespace TauCeti

variable {p : ℝ}

/-- The orthogonal projection of `ℂ` onto the real line `ℝ u` for any `u` with
`u² = toCircle θ`: the real-linear map `w ↦ (w + z * conj w) / 2`, `z = toCircle θ`. Its ranges
are the fibres of the Möbius line bundle. -/
noncomputable def mobiusProjection (θ : AddCircle p) : ℂ →L[ℝ] ℂ :=
  (2⁻¹ : ℝ) • (ContinuousLinearMap.id ℝ ℂ +
    (AddCircle.toCircle θ : ℂ) • (conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap)

/-- `mobiusProjection θ w = (w + z * conj w) / 2` for `z = toCircle θ`. -/
theorem mobiusProjection_apply (θ : AddCircle p) (w : ℂ) :
    mobiusProjection θ w = 2⁻¹ * (w + AddCircle.toCircle θ * conj w) := by
  simp [mobiusProjection, Complex.real_smul]
  ring

/-- The projections `mobiusProjection θ` depend continuously on `θ`. -/
theorem continuous_mobiusProjection : Continuous (mobiusProjection (p := p)) := by
  unfold mobiusProjection
  fun_prop

private theorem toCircle_mul_conj (θ : AddCircle p) :
    (AddCircle.toCircle θ : ℂ) * conj (AddCircle.toCircle θ : ℂ) = 1 := by
  rw [Complex.mul_conj, Circle.normSq_coe, Complex.ofReal_one]

/-- `mobiusProjection θ` is a projection. -/
theorem isIdempotentElem_mobiusProjection (θ : AddCircle p) :
    IsIdempotentElem (mobiusProjection θ) := by
  ext1 w
  simp only [mul_apply_eq_comp, mobiusProjection_apply, map_mul, map_add, map_inv₀,
    Complex.conj_conj, Complex.conj_ofNat]
  linear_combination (2⁻¹ * 2⁻¹ * w) * toCircle_mul_conj θ

/-- The fibre over `θ` consists of the `v` with `z * conj v = v`, `z = toCircle θ`. -/
theorem mem_range_mobiusProjection_iff {θ : AddCircle p} {v : ℂ} :
    v ∈ (mobiusProjection θ).range ↔ (AddCircle.toCircle θ : ℂ) * conj v = v := by
  simp only [LinearMap.mem_range, ContinuousLinearMap.coe_coe]
  refine ⟨?_, fun hv ↦ ⟨v, ?_⟩⟩
  · rintro ⟨w, rfl⟩
    simp only [mobiusProjection_apply, map_mul, map_add, map_inv₀, Complex.conj_conj,
      Complex.conj_ofNat]
    linear_combination (2⁻¹ * w) * toCircle_mul_conj θ
  · rw [mobiusProjection_apply, hv]
    ring

/-- The fibre over `2 • θ` contains `toCircle θ`. -/
theorem toCircle_mem_range_mobiusProjection_two_zsmul (θ : AddCircle p) :
    (AddCircle.toCircle θ : ℂ) ∈ (mobiusProjection ((2 : ℤ) • θ)).range := by
  rw [mem_range_mobiusProjection_iff, AddCircle.toCircle_zsmul, zpow_two, Circle.coe_mul]
  linear_combination (AddCircle.toCircle θ : ℂ) * toCircle_mul_conj θ

/-- The fibre over `2 • θ` is spanned by `toCircle θ`. -/
private theorem nonempty_continuousLinearEquiv_range_mobiusProjection_two_zsmul (θ : AddCircle p) :
    Nonempty (ℝ ≃L[ℝ] (mobiusProjection ((2 : ℤ) • θ)).range) := by
  let f : ℝ →ₗ[ℝ] (mobiusProjection ((2 : ℤ) • θ)).range :=
    LinearMap.toSpanSingleton ℝ _ ⟨_, toCircle_mem_range_mobiusProjection_two_zsmul θ⟩
  refine ⟨(LinearEquiv.ofBijective f ⟨fun s t hst ↦ ?_, fun v ↦ ?_⟩).toContinuousLinearEquiv⟩
  · have := congrArg Subtype.val hst
    simp only [f, LinearMap.toSpanSingleton_apply, Submodule.coe_smul] at this
    exact smul_left_injective ℝ (Circle.coe_ne_zero _) this
  · obtain ⟨v, hv⟩ := v
    have hv' := mem_range_mobiusProjection_iff.1 hv
    rw [AddCircle.toCircle_zsmul, zpow_two, Circle.coe_mul] at hv'
    have huu := toCircle_mul_conj θ
    refine ⟨(v * conj (AddCircle.toCircle θ : ℂ)).re, Subtype.ext ?_⟩
    simp only [f, LinearMap.toSpanSingleton_apply, Submodule.coe_smul, Complex.real_smul]
    -- `v * conj u` is real for `u = toCircle θ`, since `u² * conj v = v`.
    have hre : ((v * conj (AddCircle.toCircle θ : ℂ)).re : ℂ) =
        v * conj (AddCircle.toCircle θ : ℂ) := by
      rw [Complex.re_eq_add_conj, map_mul, Complex.conj_conj]
      linear_combination 2⁻¹ * (conj (AddCircle.toCircle θ : ℂ) * hv' -
        AddCircle.toCircle θ * conj v * huu)
    rw [hre]
    linear_combination v * huu

/-- Every fibre of the Möbius line bundle is a real line. -/
theorem nonempty_continuousLinearEquiv_range_mobiusProjection (θ : AddCircle p) :
    Nonempty (ℝ ≃L[ℝ] (mobiusProjection θ).range) := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective θ
  have hθ : ((x : ℝ) : AddCircle p) = (2 : ℤ) • ((x / 2 : ℝ) : AddCircle p) := by
    rw [← AddCircle.coe_zsmul]
    congr 1
    simp only [zsmul_eq_mul, Int.cast_ofNat]
    ring
  rw [hθ]
  exact nonempty_continuousLinearEquiv_range_mobiusProjection_two_zsmul _

variable (p) in
/-- The fibre over `θ` of the **Möbius line bundle** over the circle `AddCircle p`: the real line
`ℝ u ⊆ ℂ` for `u² = toCircle θ`. As `θ` goes once around the circle, `u` turns through half a
turn, so the line returns to itself with its orientation reversed. -/
abbrev MobiusLine (θ : AddCircle p) : Type := (mobiusProjection θ).range

/-- The total space of the Möbius line bundle carries the topology of a subspace of
`AddCircle p × ℂ`. -/
noncomputable instance : TopologicalSpace (TotalSpace ℝ (MobiusLine p)) :=
  instTopologicalSpaceTotalSpaceRange ℝ mobiusProjection

/-- The Möbius line bundle is a fibre bundle with model fibre `ℝ`, trivialized by the intertwining
operators of the projections `mobiusProjection θ`. -/
noncomputable instance : FiberBundle ℝ (MobiusLine p) :=
  rangeFiberBundle continuous_mobiusProjection isIdempotentElem_mobiusProjection
    nonempty_continuousLinearEquiv_range_mobiusProjection

instance : VectorBundle ℝ ℝ (MobiusLine p) :=
  rangeVectorBundle continuous_mobiusProjection isIdempotentElem_mobiusProjection
    nonempty_continuousLinearEquiv_range_mobiusProjection

/-- The total space of the Möbius line bundle is a subspace of `AddCircle p × ℂ`. -/
theorem isEmbedding_totalSpace_mobiusLine :
    Topology.IsEmbedding fun v : TotalSpace ℝ (MobiusLine p) ↦ (v.proj, (v.2 : ℂ)) :=
  isEmbedding_totalSpace_range ℝ mobiusProjection

/-- Two vectors of the Möbius line bundle are equal when they have the same base point and the
same value in `ℂ`. -/
theorem totalSpace_mobiusLine_ext {v w : TotalSpace ℝ (MobiusLine p)} (h₁ : v.proj = w.proj)
    (h₂ : (v.2 : ℂ) = w.2) : v = w :=
  isEmbedding_totalSpace_mobiusLine.injective (Prod.ext h₁ h₂)

/-- The fibre norm of the Möbius line bundle is continuous on the total space. -/
theorem continuous_norm_mobiusLine : Continuous fun v : TotalSpace ℝ (MobiusLine p) ↦ ‖v.2‖ :=
  continuous_norm.comp (continuous_snd.comp isEmbedding_totalSpace_mobiusLine.continuous)

variable [Fact (0 < p)]

/-- **The unit circle bundle of the Möbius line is a circle double covering the base**: the
homeomorphism `θ ↦ (2 • θ, toCircle θ)` from `AddCircle p` onto the unit vectors, under which the
bundle projection is `θ ↦ 2 • θ` (`TauCeti.proj_mobiusSphereHomeomorph`). -/
noncomputable def mobiusSphereHomeomorph : AddCircle p ≃ₜ sphereBundle ℝ (MobiusLine p) where
  toFun θ := ⟨⟨(2 : ℤ) • θ, ⟨_, toCircle_mem_range_mobiusProjection_two_zsmul θ⟩⟩, by simp⟩
  invFun v := (AddCircle.homeomorphCircle (Fact.out : 0 < p).ne').symm
    ⟨v.1.2, mem_sphere_zero_iff_norm.2 (mem_sphereBundle.1 v.2)⟩
  left_inv θ := (Homeomorph.symm_apply_eq _).2 (AddCircle.homeomorphCircle_apply _ θ).symm
  right_inv v := by
    have hp : p ≠ 0 := (Fact.out : 0 < p).ne'
    set u : Circle := ⟨v.1.2, mem_sphere_zero_iff_norm.2 (mem_sphereBundle.1 v.2)⟩
    have hu : AddCircle.toCircle ((AddCircle.homeomorphCircle hp).symm u) = u := by
      rw [← AddCircle.homeomorphCircle_apply hp, Homeomorph.apply_symm_apply]
    refine Subtype.ext (totalSpace_mobiusLine_ext ?_ ?_)
    · -- The base point of a unit vector `v` is `v²`.
      refine AddCircle.injective_toCircle hp (Circle.ext ?_)
      rw [AddCircle.toCircle_zsmul, hu, zpow_two, Circle.coe_mul]
      have hv : (AddCircle.toCircle v.1.proj : ℂ) * conj (u : ℂ) = u :=
        mem_range_mobiusProjection_iff.1 v.1.2.2
      have huu : (u : ℂ) * conj (u : ℂ) = 1 := by
        rw [Complex.mul_conj, Circle.normSq_coe, Complex.ofReal_one]
      linear_combination -(u : ℂ) * hv + AddCircle.toCircle v.1.proj * huu
    · exact congrArg Subtype.val hu
  continuous_toFun := by
    refine Continuous.subtype_mk (isEmbedding_totalSpace_mobiusLine.continuous_iff.2 ?_) _
    exact (continuous_const_smul _).prodMk
      (continuous_subtype_val.comp AddCircle.continuous_toCircle)
  continuous_invFun := by
    refine (Homeomorph.continuous _).comp (Continuous.subtype_mk ?_ _)
    exact continuous_snd.comp
      (isEmbedding_totalSpace_mobiusLine.continuous.comp continuous_subtype_val)

/-- The bundle projection of the unit vector `mobiusSphereHomeomorph θ` is `2 • θ`. -/
@[simp]
theorem proj_mobiusSphereHomeomorph (θ : AddCircle p) :
    (mobiusSphereHomeomorph θ : TotalSpace ℝ (MobiusLine p)).proj = (2 : ℤ) • θ :=
  (rfl)

/-- The unit vector `mobiusSphereHomeomorph θ` is `toCircle θ ∈ ℂ`. -/
@[simp]
theorem coe_snd_mobiusSphereHomeomorph (θ : AddCircle p) :
    ((mobiusSphereHomeomorph θ : TotalSpace ℝ (MobiusLine p)).2 : ℂ) = AddCircle.toCircle θ :=
  (rfl)

/-- The unit vector `v ∈ ℂ` is `toCircle` of the point `mobiusSphereHomeomorph.symm v`. -/
@[simp]
theorem coe_toCircle_mobiusSphereHomeomorph_symm (v : sphereBundle ℝ (MobiusLine p)) :
    (AddCircle.toCircle (mobiusSphereHomeomorph.symm v) : ℂ) = v.1.2 := by
  rw [← coe_snd_mobiusSphereHomeomorph, Homeomorph.apply_symm_apply]

/-! ### The relative homology of the Thom pair -/

open AlgebraicTopology

/-- The circle `θ ↦ (2 • θ, toCircle θ)` in the nonzero vectors of the Möbius line. -/
private noncomputable def mobiusCircleHom :
    TopCat.of (AddCircle p) ⟶ (thomPair ℝ (MobiusLine p)).snd :=
  TopCat.ofHom
    ((ContinuousMap.inclusion (sphereBundle_subset_zeroSectionCompl ℝ (MobiusLine p))).comp
      ⟨mobiusSphereHomeomorph (p := p), mobiusSphereHomeomorph.continuous⟩)

/-- The bundle projection of the Möbius line. -/
private noncomputable def mobiusProjHom :
    (thomPair ℝ (MobiusLine p)).fst ⟶ TopCat.of (AddCircle p) :=
  TopCat.ofHom ⟨TotalSpace.proj, FiberBundle.continuous_proj ℝ (MobiusLine p)⟩

/-- The doubling map `θ ↦ 2 • θ` of the circle. -/
private noncomputable def doublingHom : TopCat.of (AddCircle p) ⟶ TopCat.of (AddCircle p) :=
  TopCat.ofHom ⟨fun θ : AddCircle p ↦ (2 : ℤ) • θ, continuous_zsmul 2⟩

/-- The circle of unit vectors projects to the base as the doubling map. -/
private theorem mobiusCircleHom_comp_map_comp_mobiusProjHom :
    mobiusCircleHom ≫ (thomPair ℝ (MobiusLine p)).map ≫ mobiusProjHom = doublingHom (p := p) :=
  rfl

private instance (n : ℕ) : IsIso (SSet.homologyMap (TopCat.toSSet.map (mobiusProjHom (p := p)))
    (ModuleCat.of ℤ ℤ) n) := by
  have h : mobiusProjHom (p := p) =
      TopCat.ofHom (VectorBundle.totalSpaceHomotopyEquiv ℝ (MobiusLine p)).toFun := by
    ext v
    exact (VectorBundle.totalSpaceHomotopyEquiv_apply v).symm
  have := ((VectorBundle.totalSpaceHomotopyEquiv ℝ (MobiusLine p)).singularHomologyIso
    (ModuleCat.of ℤ ℤ) n).isIso_hom
  rw [ContinuousMap.HomotopyEquiv.singularHomologyIso_hom] at this
  exact (congrArg (fun f ↦ IsIso (SSet.homologyMap (TopCat.toSSet.map f) (ModuleCat.of ℤ ℤ) n))
    h).mpr this

private instance (n : ℕ) : IsIso (SSet.homologyMap (TopCat.toSSet.map (mobiusCircleHom (p := p)))
    (ModuleCat.of ℤ ℤ) n) := by
  set e := sphereBundleHomotopyEquiv ℝ (MobiusLine p) continuous_norm_mobiusLine
  have h : mobiusCircleHom (p := p) =
      (TopCat.isoOfHomeo mobiusSphereHomeomorph).hom ≫ TopCat.ofHom e.toFun := by
    ext θ
    exact Subtype.ext (coe_sphereBundleHomotopyEquiv ℝ (MobiusLine p) _ _).symm
  have := IsIso.comp_isIso' (Functor.map_isIso ((singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj
    (ModuleCat.of ℤ ℤ)) (TopCat.isoOfHomeo (X := TopCat.of (AddCircle p))
      (Y := TopCat.of (sphereBundle ℝ (MobiusLine p))) mobiusSphereHomeomorph).hom)
      (e.singularHomologyIso (ModuleCat.of ℤ ℤ) n).isIso_hom
  rw [ContinuousMap.HomotopyEquiv.singularHomologyIso_hom, ← Functor.map_comp] at this
  exact (congrArg (fun f ↦ IsIso (SSet.homologyMap (TopCat.toSSet.map f) (ModuleCat.of ℤ ℤ) n))
    h).mpr this

/-- The inclusion of the nonzero vectors induces an isomorphism on zeroth homology. -/
private theorem mono_homologyMap_map_thomPair_mobiusLine_zero :
    Mono (SSet.homologyMap (TopCat.toSSet.map (thomPair ℝ (MobiusLine p)).map)
      (ModuleCat.of ℤ ℤ) 0) := by
  have h : SSet.homologyMap (TopCat.toSSet.map (mobiusCircleHom (p := p))) (ModuleCat.of ℤ ℤ) 0 ≫
      SSet.homologyMap (TopCat.toSSet.map (thomPair ℝ (MobiusLine p)).map) (ModuleCat.of ℤ ℤ) 0 ≫
      SSet.homologyMap (TopCat.toSSet.map mobiusProjHom) (ModuleCat.of ℤ ℤ) 0 = 𝟙 _ := by
    rw [← SSet.homologyMap_comp, ← SSet.homologyMap_comp, ← Functor.map_comp, ← Functor.map_comp,
      mobiusCircleHom_comp_map_comp_mobiusProjHom, ← singularHomologyFunctor_obj_map]
    exact singularHomology₀_map_eq_id_of_pathConnectedSpace _ _
  -- With `s` and `q` invertible, `i = s⁻¹ ≫ q⁻¹`.
  rw [← IsIso.eq_inv_comp, Category.comp_id, ← IsIso.eq_comp_inv] at h
  rw [h]
  infer_instance

/-- The inclusion of the nonzero vectors acts on first homology as the doubling map of the
circle. -/
private theorem firstHomologyEquiv_homologyMap_mobiusProjHom_map_mobiusCircleHom
    (x : ((singularChains ℤ).obj (TopCat.of (AddCircle p))).homology 1) :
    AddCircle.firstHomologyEquiv
      ((SSet.homologyMap (TopCat.toSSet.map mobiusProjHom) (ModuleCat.of ℤ ℤ) 1).hom
        ((SSet.homologyMap (TopCat.toSSet.map (thomPair ℝ (MobiusLine p)).map)
          (ModuleCat.of ℤ ℤ) 1).hom
          ((SSet.homologyMap (TopCat.toSSet.map mobiusCircleHom) (ModuleCat.of ℤ ℤ) 1).hom x))) =
      2 * AddCircle.firstHomologyEquiv x := by
  have h := congrArg (fun f ↦ (SSet.homologyMap (TopCat.toSSet.map f) (ModuleCat.of ℤ ℤ) 1).hom x)
    (mobiusCircleHom_comp_map_comp_mobiusProjHom (p := p))
  simp only [Functor.map_comp, SSet.homologyMap_comp, ModuleCat.hom_comp] at h
  exact (congrArg AddCircle.firstHomologyEquiv h).trans
    (AddCircle.firstHomologyEquiv_singularHomologyMap_zsmul 2 x)

/-- **The first relative integral homology of the Thom pair of the Möbius line is `ℤ/2`.** The
Thom pair is the total space relative to the nonzero vectors. -/
theorem nonempty_linearEquiv_singularHomology_thomPair_mobiusLine_one :
    Nonempty (((thomPair ℝ (MobiusLine p)).singularHomology (ModuleCat.of ℤ ℤ) 1 : ModuleCat.{0} ℤ)
      ≃ₗ[ℤ] ZMod 2) := by
  -- The connecting map to `H₀(E₀)` vanishes, since `H₀(E₀) → H₀(E)` is injective.
  have hδ : (thomPair ℝ (MobiusLine p)).singularHomologyδ (ModuleCat.of ℤ ℤ) 1 0 = 0 :=
    (mono_homologyMap_map_thomPair_mobiusLine_zero (p := p)).right_cancellation _ _
      (((thomPair ℝ (MobiusLine p)).singularHomologyδ_comp (ModuleCat.of ℤ ℤ) 1 0).trans
        Limits.zero_comp.symm)
  have hπ : Function.Surjective
      ((thomPair ℝ (MobiusLine p)).singularHomologyπ (ModuleCat.of ℤ ℤ) 1).hom := by
    rw [← ModuleCat.epi_iff_surjective]
    exact ((thomPair ℝ (MobiusLine p)).singularHomology_exact_relative (ModuleCat.of ℤ ℤ) 1 0).epi_f
      hδ
  -- Reduce `H₁(E)` modulo `2` through the projection to the circle and `H₁(S¹) ≃ ℤ`.
  let q : (TopPair.toSSetPair.obj (thomPair ℝ (MobiusLine p))).right.homology
      (ModuleCat.of ℤ ℤ) 1 ⟶ ((singularChains ℤ).obj (TopCat.of (AddCircle p))).homology 1 :=
    SSet.homologyMap (TopCat.toSSet.map (mobiusProjHom (p := p))) (ModuleCat.of ℤ ℤ) 1
  have hq : Function.Bijective q.hom :=
    (ConcreteCategory.isIso_iff_bijective q).1 (inferInstanceAs (IsIso (SSet.homologyMap
      (TopCat.toSSet.map (mobiusProjHom (p := p))) (ModuleCat.of ℤ ℤ) 1)))
  let g := (Int.castAddHom (ZMod 2)).comp
    (AddCircle.firstHomologyEquiv.toLinearMap ∘ₗ q.hom).toAddMonoidHom
  have hg : Function.Surjective g := by
    intro c
    obtain ⟨n, rfl⟩ := ZMod.intCast_surjective c
    obtain ⟨y, hy⟩ := hq.2 (AddCircle.firstHomologyEquiv.symm n)
    refine ⟨y, ?_⟩
    simp only [g, AddMonoidHom.coe_comp, Function.comp_apply, LinearMap.toAddMonoidHom_coe,
      LinearMap.coe_comp, LinearEquiv.coe_coe, hy, LinearEquiv.apply_symm_apply,
      Int.coe_castAddHom]
  have hs : Function.Surjective (SSet.homologyMap (TopCat.toSSet.map (mobiusCircleHom (p := p)))
      (ModuleCat.of ℤ ℤ) 1).hom := by
    rw [← ModuleCat.epi_iff_surjective]
    infer_instance
  -- The kernel of `H₁(E) → H₁(E, E₀)` is the image of `H₁(E₀)`, which is `2ℤ` in `H₁(S¹) ≃ ℤ`.
  have hker :
      ((thomPair ℝ (MobiusLine p)).singularHomologyπ (ModuleCat.of ℤ ℤ) 1).hom.toAddMonoidHom.ker =
        g.ker := by
    ext y
    have hexact := SetLike.ext_iff.1 ((ShortComplex.moduleCat_exact_iff_range_eq_ker _).1
      ((thomPair ℝ (MobiusLine p)).singularHomology_exact_space (ModuleCat.of ℤ ℤ) 1)) y
    have h₁ : ((thomPair ℝ (MobiusLine p)).singularHomologyπ (ModuleCat.of ℤ ℤ) 1).hom y = 0 ↔
        ∃ z, (SSet.homologyMap (TopCat.toSSet.map (thomPair ℝ (MobiusLine p)).map)
          (ModuleCat.of ℤ ℤ) 1).hom z = y :=
      hexact.symm
    have h₂ : g y = 0 ↔ 2 ∣ AddCircle.firstHomologyEquiv (q.hom y) :=
      ZMod.intCast_zmod_eq_zero_iff_dvd _ 2
    rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_ker, LinearMap.toAddMonoidHom_coe, h₁, h₂]
    constructor
    · rintro ⟨z, rfl⟩
      obtain ⟨x, rfl⟩ := hs z
      exact ⟨_, firstHomologyEquiv_homologyMap_mobiusProjHom_map_mobiusCircleHom x⟩
    · rintro ⟨n, hn⟩
      refine ⟨(SSet.homologyMap (TopCat.toSSet.map mobiusCircleHom) (ModuleCat.of ℤ ℤ) 1).hom
        (AddCircle.firstHomologyEquiv.symm n), hq.1 (AddCircle.firstHomologyEquiv.injective ?_)⟩
      refine (firstHomologyEquiv_homologyMap_mobiusProjHom_map_mobiusCircleHom _).trans ?_
      rw [LinearEquiv.apply_symm_apply, hn]
  exact ⟨((QuotientAddGroup.quotientKerEquivOfSurjective
    ((thomPair ℝ (MobiusLine p)).singularHomologyπ (ModuleCat.of ℤ ℤ) 1).hom.toAddMonoidHom
      hπ).symm.trans <|
    (QuotientAddGroup.quotientAddEquivOfEq hker).trans <|
      QuotientAddGroup.quotientKerEquivOfSurjective g hg).toIntLinearEquiv⟩

/-- **Constant coefficients give the wrong group.** The first relative integral homology of the
Thom pair of the Möbius line is not the zeroth integral homology `ℤ` of the base circle. -/
theorem not_nonempty_linearEquiv_singularHomology_thomPair_mobiusLine_one_zero :
    ¬ Nonempty (((thomPair ℝ (MobiusLine p)).singularHomology (ModuleCat.of ℤ ℤ) 1 :
      ModuleCat.{0} ℤ) ≃ₗ[ℤ] ((singularChains ℤ).obj (TopCat.of (AddCircle p))).homology 0) := by
  rintro ⟨e⟩
  obtain ⟨f⟩ := nonempty_linearEquiv_singularHomology_thomPair_mobiusLine_one (p := p)
  -- The zeroth homology of the path-connected circle is `ℤ`, through the augmentation.
  have : Finite ℤ := Finite.of_equiv (ZMod 2) ((f.symm.trans e).trans (asIso
    ((TopCat.of (AddCircle p)).singularHomology₀ε (ModuleCat.of ℤ ℤ))).toLinearEquiv).toEquiv
  exact not_finite ℤ

end TauCeti
