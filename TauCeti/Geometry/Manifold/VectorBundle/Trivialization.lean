/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.Geometry.Manifold.ContMDiffMap
public import Mathlib.Geometry.Manifold.VectorBundle.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Submersion

/-!
# The fibre coordinate and partial diffeomorphism of a bundle trivialization

Near a point `v₀` of the total space of a fibre bundle, every point can be read in the preferred
trivialization at the base point `v₀.proj`. For a `C^n` model of the total space, the fibre
coordinate of such a point in that trivialization is `C^n` at `v₀`. That points near `v₀` lie over
the base set of the trivialization is the topological fact
`Bundle.TotalSpace.eventually_proj_mem_baseSet_trivializationAt`.

For a vector bundle, the same reading applies to a `C^n` map from a normed space into the total
space: its fibre part, read through the linear map of the trivialization at the image of the base
point, is a `C^n` map between normed spaces there. Read in the same way, the inclusion of a fibre
into the total space is a continuous linear isomorphism onto the model fibre; hence it is `C^n`
and has injective derivative, whose image is the kernel of the derivative of the projection when
the fibres are finite-dimensional. Moreover, every atlas trivialization of a `C^n`
vector bundle is a `C^n` partial diffeomorphism between its source in `TotalSpace F E` and its
target `e.baseSet ×ˢ univ` in `B × F`, and hence a `C^n` local diffeomorphism in both directions.
Read back through such a trivialization, a `C^n` family of vectors of the model fibre is a `C^n`
section.

## Main results

* `Bundle.TotalSpace.contMDiffAt_trivializationAt_snd`: the fibre coordinate in the
  trivialization at `v₀.proj` is `C^n` at `v₀`.
* `ContMDiffAt.contDiffAt_continuousLinearMapAt_trivializationAt`: a `C^n` map from a normed space
  into the total space of a vector bundle has `C^n` fibre coordinates in the trivialization at the
  base point of its value.
* `TauCeti.Manifold.contMDiff_totalSpaceMk`, `TauCeti.Manifold.injective_mfderiv_totalSpaceMk`:
  the inclusion of a fibre into the total space of a vector bundle is `C^n` and has injective
  derivative.
* `TauCeti.Manifold.ker_mfderiv_proj_eq_range_mfderiv_totalSpaceMk`: for finite-dimensional
  fibres, the vertical tangent vectors, those killed by the derivative of the projection, are the
  derivatives of the inclusion of the fibre.
* `Bundle.Trivialization.toPartialDiffeomorph`, `Bundle.Trivialization.isLocalDiffeomorphAt`,
  `Bundle.Trivialization.isLocalDiffeomorphAt_symm`: an atlas trivialization of a `C^n` vector
  bundle as a `C^n` partial diffeomorphism and local diffeomorphism.
* `Bundle.Trivialization.contMDiffOn_section_symm`: a `C^n` family of vectors of the model fibre,
  read through an atlas trivialization, is a `C^n` section over its base set.
-/

public noncomputable section

open Bundle
open scoped Manifold

namespace Bundle.TotalSpace

variable {n : WithTop ℕ∞} {𝕜 B F : Type*} {E : B → Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [TopologicalSpace (TotalSpace F E)]
  [∀ x, TopologicalSpace (E x)] {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B]
  [ChartedSpace HB B] [FiberBundle F E]

/-- The fibre coordinate in the trivialization at `v₀.proj` is `C^n` at `v₀`. -/
theorem contMDiffAt_trivializationAt_snd (v₀ : TotalSpace F E) :
    ContMDiffAt (IB.prod 𝓘(𝕜, F)) 𝓘(𝕜, F) n
      (fun v ↦ (trivializationAt F E v₀.proj v).2) v₀ :=
  (contMDiffAt_totalSpace.1 contMDiffAt_id).2

end Bundle.TotalSpace

namespace ContMDiffAt

variable {n : WithTop ℕ∞} {𝕜 B F : Type*} {E : B → Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [TopologicalSpace (TotalSpace F E)]
  [∀ x, TopologicalSpace (E x)] [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜 (E x)]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B]
  [ChartedSpace HB B] [FiberBundle F E] [VectorBundle 𝕜 F E]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G] {b : G → B} {s : ∀ z, E (b z)} {z₀ : G}

/-- A `C^n` map `z ↦ (b z, s z)` from a normed space into the total space of a vector bundle has
`C^n` fibre coordinates in the trivialization at `b z₀`, read through its linear map. -/
theorem contDiffAt_continuousLinearMapAt_trivializationAt
    (h : ContMDiffAt 𝓘(𝕜, G) (IB.prod 𝓘(𝕜, F)) n (fun z ↦ TotalSpace.mk' F (b z) (s z)) z₀) :
    ContDiffAt 𝕜 n (fun z ↦ (trivializationAt F E (b z₀)).continuousLinearMapAt 𝕜 (b z) (s z))
      z₀ := by
  refine (contMDiffAt_iff_contDiffAt.mp (contMDiffAt_totalSpace.mp h).2).congr_of_eventuallyEq ?_
  filter_upwards [(contMDiffAt_totalSpace.mp h).1.continuousAt.preimage_mem_nhds
    ((trivializationAt F E (b z₀)).open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt F E _))] with z hz
  exact (trivializationAt F E (b z₀)).continuousLinearMapAt_apply_of_mem (R := 𝕜) hz _

end ContMDiffAt

namespace TauCeti.Manifold

variable {n : WithTop ℕ∞} {𝕜 B F : Type*} {E : B → Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [TopologicalSpace (TotalSpace F E)]
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace 𝕜 (E x)]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B]
  [ChartedSpace HB B] [FiberBundle F E] [VectorBundle 𝕜 F E]

/-- The inclusion of a fibre into the total space of a vector bundle is `C^n`: read in the
trivialization at the base point, it is a continuous linear map into the model fibre. -/
theorem contMDiff_totalSpaceMk (b : B) :
    ContMDiff 𝓘(𝕜, E b) (IB.prod 𝓘(𝕜, F)) n (TotalSpace.mk b : E b → TotalSpace F E) := by
  let e := trivializationAt F E b
  have hb : b ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt F E b
  intro y
  refine contMDiffAt_totalSpace.2 ⟨contMDiffAt_const, ?_⟩
  exact (e.continuousLinearMapAt 𝕜 b).contMDiff.contMDiffAt.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun y' ↦ (e.continuousLinearMapAt_apply_of_mem 𝕜 hb y').symm)

/-- The inclusion of a fibre into the total space of a vector bundle has injective derivative:
composed with the fibre coordinate of the trivialization at the base point, it is the linear
isomorphism of that fibre with the model fibre. -/
theorem injective_mfderiv_totalSpaceMk (b : B) (y : E b) :
    Function.Injective
      (mfderiv 𝓘(𝕜, E b) (IB.prod 𝓘(𝕜, F)) (TotalSpace.mk b : E b → TotalSpace F E) y) := by
  let e := trivializationAt F E b
  have hb : b ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt F E b
  have hι : MDifferentiableAt 𝓘(𝕜, E b) (IB.prod 𝓘(𝕜, F))
      (TotalSpace.mk b : E b → TotalSpace F E) y :=
    ((contMDiff_totalSpaceMk (n := 1) b).mdifferentiable one_ne_zero) y
  have hσ : MDifferentiableAt (IB.prod 𝓘(𝕜, F)) 𝓘(𝕜, F) (fun z : TotalSpace F E ↦ (e z).2)
      (TotalSpace.mk b y) :=
    (Bundle.TotalSpace.contMDiffAt_trivializationAt_snd (n := 1) (IB := IB)
      (TotalSpace.mk' F b y)).mdifferentiableAt one_ne_zero
  have hcomp : (fun z : TotalSpace F E ↦ (e z).2) ∘ (TotalSpace.mk b : E b → TotalSpace F E) =
      e.continuousLinearMapAt 𝕜 b :=
    funext fun y' ↦ (e.continuousLinearMapAt_apply_of_mem 𝕜 hb y').symm
  intro w₁ w₂ hw
  -- After the fibre coordinate, the derivative is the injective map `e.continuousLinearMapAt`.
  have h := congrArg (mfderiv (IB.prod 𝓘(𝕜, F)) 𝓘(𝕜, F) (fun z : TotalSpace F E ↦ (e z).2)
    (TotalSpace.mk b y)) hw
  rw [← mfderiv_comp_apply y hσ hι, ← mfderiv_comp_apply y hσ hι, hcomp,
    ContinuousLinearMap.mfderiv_eq] at h
  exact (e.symmL_continuousLinearMapAt (R := 𝕜) hb w₁).symm.trans
    ((congrArg (e.symmL 𝕜 b) h).trans (e.symmL_continuousLinearMapAt (R := 𝕜) hb w₂))

/-- **The vertical tangent space of a vector bundle with finite-dimensional fibres.** At a point
`⟨b, y⟩` of the total space, the kernel of the derivative of the projection is the image of the
derivative of the inclusion of the fibre over `b`. -/
theorem ker_mfderiv_proj_eq_range_mfderiv_totalSpaceMk [FiniteDimensional 𝕜 F] (b : B) (y : E b) :
    (mfderiv (IB.prod 𝓘(𝕜, F)) IB (π F E) ⟨b, y⟩).ker =
      (mfderiv 𝓘(𝕜, E b) (IB.prod 𝓘(𝕜, F)) (TotalSpace.mk b : E b → TotalSpace F E) y).range := by
  have hb : b ∈ (trivializationAt F E b).baseSet := FiberBundle.mem_baseSet_trivializationAt F E b
  have hπ : MDifferentiableAt (IB.prod 𝓘(𝕜, F)) IB (π F E) ⟨b, y⟩ :=
    (Bundle.contMDiff_proj E (n := 1) _).mdifferentiableAt one_ne_zero
  have hι : MDifferentiableAt 𝓘(𝕜, E b) (IB.prod 𝓘(𝕜, F))
      (TotalSpace.mk b : E b → TotalSpace F E) y :=
    ((contMDiff_totalSpaceMk (n := 1) b).mdifferentiable one_ne_zero) y
  -- The kernel is the model fibre `F`, read in the preferred chart at `⟨b, y⟩`.
  let ιF : F →ₗ[𝕜] TangentSpace (IB.prod 𝓘(𝕜, F)) (⟨b, y⟩ : TotalSpace F E) :=
    LinearMap.inr 𝕜 EB F
  have hker : (mfderiv (IB.prod 𝓘(𝕜, F)) IB (π F E) ⟨b, y⟩).ker = ιF.range := by
    rw [Bundle.mfderiv_proj]
    exact LinearMap.ker_fst 𝕜 EB F
  have : FiniteDimensional 𝕜 (mfderiv (IB.prod 𝓘(𝕜, F)) IB (π F E) ⟨b, y⟩).ker := by
    rw [hker]
    exact LinearMap.finiteDimensional_range _
  -- The image lies in the kernel since the projection is constant on the fibre, and both have
  -- the dimension of `F`.
  refine (Submodule.eq_of_le_of_finrank_eq ?_ ?_).symm
  · rintro _ ⟨w, rfl⟩
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, ContinuousLinearMap.coe_coe,
      ← mfderiv_comp_apply y hπ hι]
    have hfun : (π F E ∘ (TotalSpace.mk b : E b → TotalSpace F E)) = fun _ ↦ b := rfl
    rw [hfun, mfderiv_const]
    rfl
  · rw [LinearMap.finrank_range_of_inj (injective_mfderiv_totalSpaceMk b y), hker,
      LinearMap.finrank_range_of_inj (f := ιF) LinearMap.inr_injective]
    exact ((trivializationAt F E b).continuousLinearEquivAt 𝕜 b hb).toLinearEquiv.finrank_eq

end TauCeti.Manifold

namespace Bundle.Trivialization

variable {𝕜 B F : Type*} {E : B → Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [TopologicalSpace (TotalSpace F E)]
  [∀ x, TopologicalSpace (E x)] [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜 (E x)]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB] (IB : ModelWithCorners 𝕜 EB HB) [TopologicalSpace B]
  [ChartedSpace HB B] (n : WithTop ℕ∞) [FiberBundle F E] [VectorBundle 𝕜 F E]
  [ContMDiffVectorBundle n F E IB]
  (e : Trivialization F (π F E)) [MemTrivializationAtlas e]

/-- An atlas trivialization of a `C^n` vector bundle as a `C^n` partial diffeomorphism between
its open source in `TotalSpace F E` and its open target `e.baseSet ×ˢ univ` in `B × F`. -/
def toPartialDiffeomorph :
    PartialDiffeomorph (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, F)) (TotalSpace F E) (B × F) n where
  toPartialEquiv := e.toPartialEquiv
  open_source := e.open_source
  open_target := e.open_target
  contMDiffOn_toFun := e.contMDiffOn
  contMDiffOn_invFun := e.contMDiffOn_symm

/-- The underlying `PartialEquiv` of `e.toPartialDiffeomorph` is `e.toPartialEquiv`. -/
@[simp]
theorem toPartialDiffeomorph_toPartialEquiv :
    (e.toPartialDiffeomorph IB n).toPartialEquiv = e.toPartialEquiv := (rfl)

/-- The source of `e.toPartialDiffeomorph` is `e.source`. -/
theorem toPartialDiffeomorph_source : (e.toPartialDiffeomorph IB n).source = e.source := (rfl)

/-- The target of `e.toPartialDiffeomorph` is `e.target`. -/
theorem toPartialDiffeomorph_target : (e.toPartialDiffeomorph IB n).target = e.target := (rfl)

/-- Coercing `e.toPartialDiffeomorph` to a function recovers `e`. -/
theorem coe_toPartialDiffeomorph : ⇑(e.toPartialDiffeomorph IB n) = e := e.coe_coe.symm

/-- Applying the partial inverse of `e.toPartialDiffeomorph` agrees with
`e.toOpenPartialHomeomorph.symm`. -/
theorem toPartialDiffeomorph_symm_apply (q : B × F) :
    (e.toPartialDiffeomorph IB n).toPartialEquiv.symm q = e.toOpenPartialHomeomorph.symm q := (rfl)

variable {IB n e}

/-- An atlas trivialization of a `C^n` vector bundle is a `C^n` local diffeomorphism at every
point of its source. -/
theorem isLocalDiffeomorphAt {p : TotalSpace F E} (hp : p ∈ e.source) :
    IsLocalDiffeomorphAt (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, F)) n e p :=
  TauCeti.isLocalDiffeomorphAt_of_eqOn (Φ := e.toPartialDiffeomorph IB n) hp
    fun _ _ ↦ (congrFun e.coe_coe _).symm

/-- The partial inverse of an atlas trivialization of a `C^n` vector bundle is a `C^n` local
diffeomorphism at every point of its target. -/
theorem isLocalDiffeomorphAt_symm {q : B × F} (hq : q ∈ e.target) :
    IsLocalDiffeomorphAt (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, F)) n e.toOpenPartialHomeomorph.symm q :=
  TauCeti.isLocalDiffeomorphAt_of_eqOn (Φ := (e.toPartialDiffeomorph IB n).symm) hq
    fun _ _ ↦ rfl

end Bundle.Trivialization


namespace Bundle.Trivialization

open TopologicalSpace
open scoped ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]
  {n : ℕ∞ω} [ContMDiffVectorBundle n F V I]
  (e e' : Trivialization F (π F V)) [MemTrivializationAtlas e] [MemTrivializationAtlas e']
  {U : Opens M} (hU : (U : Set M) ⊆ e.baseSet) (hU' : (U : Set M) ⊆ e'.baseSet)

/-- The actual frame-change operator as a smooth map on any common open frame domain. -/
def frameTransitionMap : C^n⟮I, U; 𝓘(𝕜, F →L[𝕜] F), F →L[𝕜] F⟯ :=
  ⟨fun x ↦ (e.coordChangeL 𝕜 e' x : F →L[𝕜] F), fun x ↦
    (contMDiffAt_coordChangeL (e := e) (e' := e') (hU x.2) (hU' x.2)).comp x
      contMDiff_subtype_val.contMDiffAt⟩

/-- Evaluation of the smooth frame-change operator is the native bundle coordinate change. -/
@[simp]
theorem frameTransitionMap_apply (x : U) :
    frameTransitionMap (I := I) (n := n) e e' hU hU' x =
      (e.coordChangeL 𝕜 e' x : F →L[𝕜] F) := by
  rfl


end Bundle.Trivialization

namespace Bundle.Trivialization

variable {𝕜 B F : Type*} {E : B → Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [TopologicalSpace (TotalSpace F E)]
  [∀ x, TopologicalSpace (E x)] [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜 (E x)]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B]
  [ChartedSpace HB B] {n : WithTop ℕ∞} [FiberBundle F E] [VectorBundle 𝕜 F E]
  [ContMDiffVectorBundle n F E IB]
  (e : Trivialization F (π F E)) [MemTrivializationAtlas e]

/-- **A `C^n` family of vectors of the model fibre, read through a trivialization, is a `C^n`
section.** Over an open subset `U` of the base set of an atlas trivialization `e`, the section
`x ↦ e.symm x (u x)` is `C^n` when `u` is. -/
theorem contMDiffOn_section_symm {U : Set B} (hU : IsOpen U) (hUe : U ⊆ e.baseSet) {u : B → F}
    (hu : ContMDiffOn IB 𝓘(𝕜, F) n u U) :
    ContMDiffOn IB (IB.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (e.symm x (u x))) U :=
  (e.contMDiffOn_section_iff hU hUe).mpr (hu.congr fun x hx ↦ by simp [e.apply_mk_symm (hUe hx)])

end Bundle.Trivialization
