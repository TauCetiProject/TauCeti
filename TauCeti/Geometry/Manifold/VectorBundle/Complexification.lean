/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import TauCeti.Geometry.Manifold.VectorBundle.Hom
public import TauCeti.Geometry.Manifold.VectorBundle.Scalar
public import TauCeti.Topology.VectorBundle.Complexification

/-!
# `C^n` complex vector bundles over real manifolds and complexification of `C^n` sections

Over a charted space `(B, IB)` modelled on a `𝕜`-normed space (most importantly `𝕜 = ℝ`), a vector
bundle `W : B → Type*` carrying compatible `VectorBundle 𝕜 G W` and `VectorBundle 𝕜' G W`
structures along a normed field extension `𝕜 ⊆ 𝕜'` (such as `ℝ ⊆ ℂ`) has `C^n` scalar
multiplication by `𝕜'`-valued maps (`ContMDiffWithinAt.algebra_smul_totalSpace` and section
variants), and its space of `C^n` global sections `Cₛ^n⟮IB; G, W⟯` inherits a `Module 𝕜'`
structure forming a scalar tower over `𝕜` (`ContMDiffSection.instModuleOfNormedAlgebra`,
`ContMDiffSection.instIsScalarTower`). When `𝕜 = ℝ` and `𝕜' = ℂ`, fibrewise multiplication by
`Complex.I` defines a `C^n` diffeomorphism of total spaces (`TauCeti.smulIDiffeomorph`) and a `C^n`
section of the real endomorphism bundle (`TauCeti.contMDiff_smulIEquiv_bundle`).

For any real `C^n` vector bundle `E : B → Type*` with model fibre `F` whose complexified fibres
`ℂ ⊗[ℝ] E x` carry `TauCeti.IsComplexificationTopology (E x)` (supplied in the
`TauCeti.Complexification` scope by `TauCeti.complexificationTopology`), we establish:

* `TauCeti.instContMDiffVectorBundleComplexification`: `fun x ↦ ℂ ⊗[ℝ] E x` is a
  `ContMDiffVectorBundle n (Complexification F) (fun x ↦ ℂ ⊗[ℝ] E x) IB` (with no finite-rank,
  completeness, or `IsManifold` assumption on `B`);
* `TauCeti.contMDiffWithinAt_complexification_totalSpace_iff` and
  `TauCeti.contMDiffWithinAt_complexification_section_iff`: maps and sections into
  `fun x ↦ ℂ ⊗[ℝ] E x` are `C^n` if and only if their real and imaginary parts into `E` are `C^n`;
* `TauCeti.tmulConjDiffeomorph` and `TauCeti.complexificationTotalSpaceDiffeomorphProd`: fibrewise
  complex conjugation and the real/imaginary-part total-space identification with `E ×ᵇ E` are
  `C^n` diffeomorphisms;
* `ContMDiffSection.complexificationEquiv`: the canonical `ℂ`-linear isomorphism
  `ℂ ⊗[ℝ] Cₛ^n⟮IB; F, E⟯ ≃ₗ[ℂ] Cₛ^n⟮IB; Complexification F, fun x ↦ ℂ ⊗[ℝ] E x⟯` identifying
  algebraically complexified `C^n` global sections of `E` with `C^n` global sections of the
  complexified bundle `fun x ↦ ℂ ⊗[ℝ] E x`, together with real/imaginary-part projections and
  conjugation on `C^n` sections.

## Main definitions and results

* `ContMDiffWithinAt.algebra_smul_totalSpace`, `ContMDiffWithinAt.algebra_smul_section`: `C^n`
  regularity of scalar multiplication by `𝕜'`-valued functions on a `𝕜'`-linear vector bundle over
  a `𝕜`-charted base.
* `ContMDiffSection.instModuleOfNormedAlgebra`, `ContMDiffSection.instIsScalarTower`: `Module 𝕜'`
  and `IsScalarTower 𝕜 𝕜'` instances on `Cₛ^n⟮IB; G, W⟯`.
* `TauCeti.smulIDiffeomorph`, `TauCeti.contMDiff_smulIEquiv_bundle`: total-space `C^n`
  diffeomorphism and Hom-bundle smoothness of multiplication by `Complex.I` on complex vector
  bundles over real manifolds.
* `TauCeti.instContMDiffVectorBundleComplexification`: `ContMDiffVectorBundle` instance on
  `fun x ↦ ℂ ⊗[ℝ] E x`.
* `TauCeti.contMDiffWithinAt_complexification_totalSpace_iff`,
  `TauCeti.contMDiffWithinAt_complexification_section_iff`: real/imaginary-part characterization of
  `C^n` maps and sections into `fun x ↦ ℂ ⊗[ℝ] E x`.
* `TauCeti.tmulConjDiffeomorph`, `TauCeti.complexificationTotalSpaceDiffeomorphProd`: `C^n`
  diffeomorphisms for fibrewise conjugation and comparison with `E ×ᵇ E`.
* `ContMDiffSection.complexificationEquiv`, `ContMDiffSection.complexificationEquivProd`,
  `ContMDiffSection.conjEquiv`: `ℂ`-linear section complexification isomorphism, real-pair
  splitting, and conjugate-linear involution on `C^n` global sections.

## References

* D. Huybrechts, *Complex Geometry: An Introduction*, Springer (2005), §1.2 and §2.6.
* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, Springer
  (1993), §10.
-/

public section

noncomputable section

open Bundle FiberBundle Filter Function Set Topology
open scoped Bundle ContDiff Manifold TensorProduct

/-! ### Scalar multiplication along a normed field extension on bundles and `C^n` sections -/

section AlgebraSMul

variable {𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜']
  [NormedAlgebra 𝕜 𝕜']
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G] [NormedSpace 𝕜' G]
  [IsScalarTower 𝕜 𝕜' G]
  {W : B → Type*} [∀ b, AddCommMonoid (W b)] [∀ b, Module 𝕜' (W b)]
  [∀ b, TopologicalSpace (W b)] [TopologicalSpace (TotalSpace G W)]
  [FiberBundle G W] [VectorBundle 𝕜' G W] {n : ℕ∞ω}
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM]
  {HM : Type*} [TopologicalSpace HM] {IM : ModelWithCorners 𝕜 EM HM}
  {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]

/-- Multiplying a bundle-valued map by a `𝕜'`-valued map preserves `C^n` regularity within a set at
a point over a `𝕜`-charted base, provided the bundle trivializations are `𝕜'`-linear. -/
theorem ContMDiffWithinAt.algebra_smul_totalSpace {a : M → 𝕜'} {g : M → TotalSpace G W}
    {s : Set M} {x : M} (ha : ContMDiffWithinAt IM 𝓘(𝕜, 𝕜') n a s x)
    (hg : ContMDiffWithinAt IM (IB.prod 𝓘(𝕜, G)) n g s x) :
    ContMDiffWithinAt IM (IB.prod 𝓘(𝕜, G)) n
      (fun y ↦ (⟨(g y).proj, a y • (g y).2⟩ : TotalSpace G W)) s x := by
  obtain ⟨hb, hv⟩ := Bundle.contMDiffWithinAt_totalSpace.mp hg
  refine Bundle.contMDiffWithinAt_totalSpace.mpr ⟨hb, ?_⟩
  let e := trivializationAt G W (g x).proj
  have he : ∀ᶠ y in 𝓝[s] x, (g y).proj ∈ e.baseSet :=
    hb.continuousWithinAt.preimage_mem_nhdsWithin
      (e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt G W (g x).proj))
  have hsmul : ContMDiffWithinAt IM 𝓘(𝕜, G) n (fun y ↦ a y • (e (g y)).2) s x :=
    (contDiff_smul (𝕜 := 𝕜) (𝕜' := 𝕜') (F := G) (n := n)).comp_contMDiffWithinAt
      (ha.prodMk_space hv)
  refine hsmul.congr_of_eventuallyEq ?_ ?_
  · filter_upwards [he] with y hy
    exact (e.linear 𝕜' hy).map_smul (a y) (g y).2
  · exact (e.linear 𝕜' (mem_baseSet_trivializationAt G W (g x).proj)).map_smul (a x) (g x).2

/-- Multiplying a bundle-valued map by a `𝕜'`-valued map preserves `C^n` regularity at a point. -/
theorem ContMDiffAt.algebra_smul_totalSpace {a : M → 𝕜'} {g : M → TotalSpace G W} {x : M}
    (ha : ContMDiffAt IM 𝓘(𝕜, 𝕜') n a x)
    (hg : ContMDiffAt IM (IB.prod 𝓘(𝕜, G)) n g x) :
    ContMDiffAt IM (IB.prod 𝓘(𝕜, G)) n
      (fun y ↦ (⟨(g y).proj, a y • (g y).2⟩ : TotalSpace G W)) x := by
  rw [← contMDiffWithinAt_univ]
  exact ha.contMDiffWithinAt.algebra_smul_totalSpace hg.contMDiffWithinAt

/-- Multiplying a bundle-valued map by a `𝕜'`-valued map preserves `C^n` regularity on a set. -/
theorem ContMDiffOn.algebra_smul_totalSpace {a : M → 𝕜'} {g : M → TotalSpace G W} {s : Set M}
    (ha : ContMDiffOn IM 𝓘(𝕜, 𝕜') n a s) (hg : ContMDiffOn IM (IB.prod 𝓘(𝕜, G)) n g s) :
    ContMDiffOn IM (IB.prod 𝓘(𝕜, G)) n
      (fun y ↦ (⟨(g y).proj, a y • (g y).2⟩ : TotalSpace G W)) s :=
  fun x hx ↦ (ha x hx).algebra_smul_totalSpace (hg x hx)

/-- Multiplying a bundle-valued map by a `𝕜'`-valued map preserves `C^n` regularity. -/
theorem ContMDiff.algebra_smul_totalSpace {a : M → 𝕜'} {g : M → TotalSpace G W}
    (ha : ContMDiff IM 𝓘(𝕜, 𝕜') n a) (hg : ContMDiff IM (IB.prod 𝓘(𝕜, G)) n g) :
    ContMDiff IM (IB.prod 𝓘(𝕜, G)) n
      (fun y ↦ (⟨(g y).proj, a y • (g y).2⟩ : TotalSpace G W)) :=
  fun x ↦ (ha x).algebra_smul_totalSpace (hg x)

/-- Multiplying a section by a `𝕜'`-valued function preserves `C^n` regularity within a set at a
point. -/
theorem ContMDiffWithinAt.algebra_smul_section {f : B → 𝕜'} {s : ∀ x, W x} {u : Set B} {x₀ : B}
    (hf : ContMDiffWithinAt IB 𝓘(𝕜, 𝕜') n f u x₀)
    (hs : ContMDiffWithinAt IB (IB.prod 𝓘(𝕜, G)) n (T% s) u x₀) :
    ContMDiffWithinAt IB (IB.prod 𝓘(𝕜, G)) n (T% (f • s)) u x₀ :=
  hf.algebra_smul_totalSpace hs

/-- Multiplying a section by a `𝕜'`-valued function preserves `C^n` regularity at a point. -/
theorem ContMDiffAt.algebra_smul_section {f : B → 𝕜'} {s : ∀ x, W x} {x₀ : B}
    (hf : ContMDiffAt IB 𝓘(𝕜, 𝕜') n f x₀)
    (hs : ContMDiffAt IB (IB.prod 𝓘(𝕜, G)) n (T% s) x₀) :
    ContMDiffAt IB (IB.prod 𝓘(𝕜, G)) n (T% (f • s)) x₀ :=
  hf.algebra_smul_totalSpace hs

/-- Multiplying a section by a `𝕜'`-valued function preserves `C^n` regularity on a set. -/
theorem ContMDiffOn.algebra_smul_section {f : B → 𝕜'} {s : ∀ x, W x} {u : Set B}
    (hf : ContMDiffOn IB 𝓘(𝕜, 𝕜') n f u)
    (hs : ContMDiffOn IB (IB.prod 𝓘(𝕜, G)) n (T% s) u) :
    ContMDiffOn IB (IB.prod 𝓘(𝕜, G)) n (T% (f • s)) u :=
  hf.algebra_smul_totalSpace hs

/-- Multiplying a section by a `𝕜'`-valued function preserves `C^n` regularity. -/
theorem ContMDiff.algebra_smul_section {f : B → 𝕜'} {s : ∀ x, W x}
    (hf : ContMDiff IB 𝓘(𝕜, 𝕜') n f)
    (hs : ContMDiff IB (IB.prod 𝓘(𝕜, G)) n (T% s)) :
    ContMDiff IB (IB.prod 𝓘(𝕜, G)) n (T% (f • s)) :=
  hf.algebra_smul_totalSpace hs

/-- Multiplying a section by a constant scalar `c : 𝕜'` preserves `C^n` regularity within a set at a
point. -/
theorem ContMDiffWithinAt.const_algebra_smul_section (c : 𝕜') {s : ∀ x, W x} {u : Set B} {x₀ : B}
    (hs : ContMDiffWithinAt IB (IB.prod 𝓘(𝕜, G)) n (T% s) u x₀) :
    ContMDiffWithinAt IB (IB.prod 𝓘(𝕜, G)) n (T% (c • s)) u x₀ :=
  contMDiffWithinAt_const.algebra_smul_section hs

/-- Multiplying a section by a constant scalar `c : 𝕜'` preserves `C^n` regularity at a point. -/
theorem ContMDiffAt.const_algebra_smul_section (c : 𝕜') {s : ∀ x, W x} {x₀ : B}
    (hs : ContMDiffAt IB (IB.prod 𝓘(𝕜, G)) n (T% s) x₀) :
    ContMDiffAt IB (IB.prod 𝓘(𝕜, G)) n (T% (c • s)) x₀ :=
  contMDiffAt_const.algebra_smul_section hs

/-- Multiplying a section by a constant scalar `c : 𝕜'` preserves `C^n` regularity on a set. -/
theorem ContMDiffOn.const_algebra_smul_section (c : 𝕜') {s : ∀ x, W x} {u : Set B}
    (hs : ContMDiffOn IB (IB.prod 𝓘(𝕜, G)) n (T% s) u) :
    ContMDiffOn IB (IB.prod 𝓘(𝕜, G)) n (T% (c • s)) u :=
  contMDiffOn_const.algebra_smul_section hs

/-- Multiplying a section by a constant scalar `c : 𝕜'` preserves `C^n` regularity. -/
theorem ContMDiff.const_algebra_smul_section (c : 𝕜') {s : ∀ x, W x}
    (hs : ContMDiff IB (IB.prod 𝓘(𝕜, G)) n (T% s)) :
    ContMDiff IB (IB.prod 𝓘(𝕜, G)) n (T% (c • s)) :=
  contMDiff_const.algebra_smul_section hs

end AlgebraSMul

namespace ContMDiffSection

section AlgebraModule

variable {𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜']
  [NormedAlgebra 𝕜 𝕜']
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G] [NormedSpace 𝕜' G]
  [IsScalarTower 𝕜 𝕜' G] {n : ℕ∞ω}
  {W : B → Type*} [TopologicalSpace (TotalSpace G W)] [∀ x, TopologicalSpace (W x)]
  [FiberBundle G W]

section SMul

variable [∀ x, AddCommMonoid (W x)] [∀ x, Module 𝕜' (W x)] [VectorBundle 𝕜' G W]

/-- Low-priority `SMul 𝕜'` instance on `C^n` sections of a `𝕜'`-linear vector bundle over a
`𝕜`-charted base; when `𝕜' = 𝕜`, `ContMDiffSection.instSMul` takes precedence and is definitionally
equal to this action. -/
instance (priority := low) instSMulOfNormedAlgebra : SMul 𝕜' Cₛ^n⟮IB; G, W⟯ :=
  ⟨fun c s ↦ ⟨c • ⇑s, s.contMDiff.const_algebra_smul_section c⟩⟩

@[simp]
theorem coe_smul_of_normedAlgebra (c : 𝕜') (s : Cₛ^n⟮IB; G, W⟯) :
    ⇑(c • s : Cₛ^n⟮IB; G, W⟯) = c • ⇑s := (rfl)

end SMul

section Module

variable [∀ x, AddCommGroup (W x)] [∀ x, Module 𝕜 (W x)] [∀ x, Module 𝕜' (W x)]
  [VectorBundle 𝕜 G W] [VectorBundle 𝕜' G W]

/-- Low-priority `Module 𝕜'` instance on `C^n` sections of a vector bundle carrying compatible `𝕜`-
and `𝕜'`-vector-bundle structures (in particular `𝕜 = ℝ`, `𝕜' = ℂ`). -/
instance (priority := low) instModuleOfNormedAlgebra : Module 𝕜' Cₛ^n⟮IB; G, W⟯ :=
  coe_injective.module 𝕜' (coeAddHom IB G n W) coe_smul_of_normedAlgebra

instance instIsScalarTower [∀ x, IsScalarTower 𝕜 𝕜' (W x)] :
    IsScalarTower 𝕜 𝕜' Cₛ^n⟮IB; G, W⟯ where
  smul_assoc r c s := ext fun x ↦ smul_assoc r c (s x)

end Module

end AlgebraModule

end ContMDiffSection

/-! ### Multiplication by `i` on complex vector bundles over real manifolds -/

namespace TauCeti

section SmulIBundle

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedSpace ℂ G]
  [IsScalarTower ℝ ℂ G] {n : ℕ∞ω}
  {W : B → Type*} [∀ x, AddCommGroup (W x)] [∀ x, Module ℂ (W x)]
  [∀ x, TopologicalSpace (W x)] [TopologicalSpace (TotalSpace G W)]
  [FiberBundle G W]

section Diffeomorph

variable (IB G n W) [VectorBundle ℂ G W]

/-- Fibrewise multiplication by `Complex.I` on a complex vector bundle over a real charted space as
a `C^n` diffeomorphism of its total space, requiring neither finite rank nor `ContMDiffVectorBundle`
nor fibrewise topological-group hypotheses. -/
def smulIDiffeomorph : TotalSpace G W ≃ₘ^n⟮IB.prod 𝓘(ℝ, G), IB.prod 𝓘(ℝ, G)⟯ TotalSpace G W where
  toFun p := ⟨p.proj, Complex.I • p.2⟩
  invFun p := ⟨p.proj, -Complex.I • p.2⟩
  left_inv := fun ⟨x, v⟩ ↦ congrArg (TotalSpace.mk x) (Complex.neg_I_smul_I_smul v)
  right_inv := fun ⟨x, v⟩ ↦ congrArg (TotalSpace.mk x) (Complex.I_smul_neg_I_smul v)
  contMDiff_toFun :=
    (contMDiff_const (c := Complex.I)).algebra_smul_totalSpace contMDiff_id
  contMDiff_invFun :=
    (contMDiff_const (c := -Complex.I)).algebra_smul_totalSpace contMDiff_id

variable {IB G n W}

@[simp]
theorem smulIDiffeomorph_apply (p : TotalSpace G W) :
    smulIDiffeomorph IB G n W p = ⟨p.proj, Complex.I • p.2⟩ := (rfl)

@[simp]
theorem smulIDiffeomorph_symm_apply (p : TotalSpace G W) :
    (smulIDiffeomorph IB G n W).symm p = ⟨p.proj, -Complex.I • p.2⟩ := (rfl)

theorem smulIDiffeomorph_apply_self (p : TotalSpace G W) :
    smulIDiffeomorph IB G n W (smulIDiffeomorph IB G n W p) = ⟨p.proj, -p.2⟩ := by
  rcases p with ⟨x, v⟩
  simp [smul_smul]

@[simp]
theorem toHomeomorph_smulIDiffeomorph [∀ x, Module ℝ (W x)] [∀ x, IsScalarTower ℝ ℂ (W x)]
    [∀ x, ContinuousConstSMul ℂ (W x)] [∀ x, IsTopologicalAddGroup (W x)]
    [∀ x, ContinuousSMul ℝ (W x)] [VectorBundle ℝ G W] :
    (smulIDiffeomorph IB G n W).toHomeomorph = smulIHomeomorph G W :=
  Homeomorph.ext fun _ ↦ by simp

end Diffeomorph

section HomBundle

variable [∀ x, Module ℝ (W x)] [∀ x, IsScalarTower ℝ ℂ (W x)] [∀ x, ContinuousConstSMul ℂ (W x)]
  [∀ x, IsTopologicalAddGroup (W x)] [∀ x, ContinuousSMul ℝ (W x)]
  [VectorBundle ℂ G W] [VectorBundle ℝ G W]

/-- Fibrewise multiplication by `Complex.I` is a `C^n` section of the real endomorphism bundle
`fun x ↦ W x →L[ℝ] W x`, with no `ContMDiffVectorBundle` or finite-rank assumption. -/
theorem contMDiff_smulIEquiv_bundle :
    ContMDiff IB (IB.prod 𝓘(ℝ, G →L[ℝ] G)) n
      (fun x ↦ TotalSpace.mk' (G →L[ℝ] G)
        (E := fun y ↦ W y →L[ℝ] W y) x (Complex.smulIEquiv (W x) : W x →L[ℝ] W x)) :=
  contMDiff_hom_bundle_of_inCoordinates_eq_const fun a _ hx _ ↦ inCoordinates_smulIEquiv a hx

/-- Fibrewise multiplication by `-Complex.I` is a `C^n` section of the real endomorphism bundle
`fun x ↦ W x →L[ℝ] W x`. -/
theorem contMDiff_smulIEquiv_symm_bundle :
    ContMDiff IB (IB.prod 𝓘(ℝ, G →L[ℝ] G)) n
      (fun x ↦ TotalSpace.mk' (G →L[ℝ] G)
        (E := fun y ↦ W y →L[ℝ] W y) x ((Complex.smulIEquiv (W x)).symm : W x →L[ℝ] W x)) :=
  contMDiff_hom_bundle_of_inCoordinates_eq_const fun a _ hx _ ↦ inCoordinates_smulIEquiv_symm a hx

end HomBundle

end SmulIBundle

/-! ### Complexification of real `C^n` vector bundles -/

section ComplexificationBundle

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ∞ω}
  {E : B → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℝ (E x)]
  [TopologicalSpace (TotalSpace F E)] [∀ x, TopologicalSpace (E x)]
  [FiberBundle F E] [VectorBundle ℝ F E]
  [∀ x, TopologicalSpace (ℂ ⊗[ℝ] E x)] [∀ x, IsComplexificationTopology (E x)]

/-- If `E` is a real `C^n` vector bundle over `(B, IB)`, then its complexification
`fun x ↦ ℂ ⊗[ℝ] E x` is a `C^n` vector bundle with model fibre `Complexification F`. Neither
`[IsManifold IB n B]` nor finite rank is needed. -/
instance instContMDiffVectorBundleComplexification [ContMDiffVectorBundle n F E IB] :
    ContMDiffVectorBundle n (Complexification F) (fun x ↦ ℂ ⊗[ℝ] E x) IB where
  contMDiffOn_coordChangeL := by
    intro e₁' e₂' he₁' he₂'
    obtain ⟨e, he, rfl⟩ := mem_trivializationAtlas_complexification_iff.mp he₁'
    obtain ⟨e', he', rfl⟩ := mem_trivializationAtlas_complexification_iff.mp he₂'
    have : MemTrivializationAtlas e := he
    have : MemTrivializationAtlas e' := he'
    let L : (F →L[ℝ] F) →L[ℝ] (Complexification F →L[ℝ] Complexification F) :=
      (ContinuousLinearMap.restrictScalarsL ℂ (Complexification F) (Complexification F) ℝ ℝ).comp
        (ContinuousLinearMap.complexifyₗᵢ F F).toContinuousLinearMap
    rw [e.baseSet_complexification, e'.baseSet_complexification]
    refine ((L.contDiff (n := n)).contMDiff.comp_contMDiffOn
      (contMDiffOn_coordChangeL (IB := IB) (n := n) e e')).congr fun b hb ↦ ?_
    simp [L, e.coordChangeL_real_complexification e' hb, ContinuousLinearMap.complexifyₗᵢ_apply]

section RegularityCharacterization

variable {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  {HM : Type*} [TopologicalSpace HM] {IM : ModelWithCorners ℝ EM HM}
  {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]

/-- A map into the total space of the complexified bundle `fun x ↦ ℂ ⊗[ℝ] E x` is `C^n` within `s`
at `x₀` if and only if its fibrewise real and imaginary parts into `TotalSpace F E` are `C^n` within
`s` at `x₀`. -/
theorem contMDiffWithinAt_complexification_totalSpace_iff
    {f : M → TotalSpace (Complexification F) fun x ↦ ℂ ⊗[ℝ] E x} {s : Set M} {x₀ : M} :
    ContMDiffWithinAt IM (IB.prod 𝓘(ℝ, Complexification F)) n f s x₀ ↔
      ContMDiffWithinAt IM (IB.prod 𝓘(ℝ, F)) n
        (fun y ↦ (⟨(f y).proj, realPart (E (f y).proj) (f y).2⟩ : TotalSpace F E)) s x₀ ∧
      ContMDiffWithinAt IM (IB.prod 𝓘(ℝ, F)) n
        (fun y ↦ (⟨(f y).proj, imaginaryPart (E (f y).proj) (f y).2⟩ : TotalSpace F E)) s x₀ := by
  simp only [Bundle.contMDiffWithinAt_totalSpace]
  have hx₀ : (f x₀).proj ∈ (trivializationAt F E (f x₀).proj).baseSet :=
    mem_baseSet_trivializationAt F E (f x₀).proj
  constructor
  · rintro ⟨hb, hf⟩
    have he : ∀ᶠ y in 𝓝[s] x₀, (f y).proj ∈ (trivializationAt F E (f x₀).proj).baseSet :=
      hb.continuousWithinAt.preimage_mem_nhdsWithin
        ((trivializationAt F E (f x₀).proj).open_baseSet.mem_nhds hx₀)
    have hre : ContMDiffWithinAt IM 𝓘(ℝ, F) n
        (fun y ↦ (Complexification.reCLM F)
          ((trivializationAt (Complexification F) (fun x ↦ ℂ ⊗[ℝ] E x)
            (f x₀).proj (f y)).2)) s x₀ :=
      (Complexification.reCLM F).contDiff.comp_contMDiffWithinAt hf
    have him : ContMDiffWithinAt IM 𝓘(ℝ, F) n
        (fun y ↦ (Complexification.imCLM F)
          ((trivializationAt (Complexification F) (fun x ↦ ℂ ⊗[ℝ] E x)
            (f x₀).proj (f y)).2)) s x₀ :=
      (Complexification.imCLM F).contDiff.comp_contMDiffWithinAt hf
    refine ⟨⟨hb, hre.congr_of_eventuallyEq ?_ ?_⟩, ⟨hb, him.congr_of_eventuallyEq ?_ ?_⟩⟩
    · filter_upwards [he] with y hy
      simp [trivializationAt_complexification, Trivialization.complexification_apply,
        Trivialization.linearMapAt_apply, hy]
    · simp [trivializationAt_complexification, Trivialization.complexification_apply,
        Trivialization.linearMapAt_apply, hx₀]
    · filter_upwards [he] with y hy
      simp [trivializationAt_complexification, Trivialization.complexification_apply,
        Trivialization.linearMapAt_apply, hy]
    · simp [trivializationAt_complexification, Trivialization.complexification_apply,
        Trivialization.linearMapAt_apply, hx₀]
  · rintro ⟨⟨hb, hre⟩, ⟨_, him⟩⟩
    refine ⟨hb, ?_⟩
    have he : ∀ᶠ y in 𝓝[s] x₀, (f y).proj ∈ (trivializationAt F E (f x₀).proj).baseSet :=
      hb.continuousWithinAt.preimage_mem_nhdsWithin
        ((trivializationAt F E (f x₀).proj).open_baseSet.mem_nhds hx₀)
    have hpair : ContMDiffWithinAt IM 𝓘(ℝ, Complexification F) n
        (fun y ↦ ((Complexification.equivProd F).symm : F × F →L[ℝ] Complexification F)
          ((trivializationAt F E (f x₀).proj ⟨(f y).proj, realPart (E (f y).proj) (f y).2⟩).2,
           (trivializationAt F E (f x₀).proj ⟨(f y).proj,
             imaginaryPart (E (f y).proj) (f y).2⟩).2)) s x₀ :=
      ((Complexification.equivProd F).symm :
        F × F →L[ℝ] Complexification F).contDiff.comp_contMDiffWithinAt (hre.prodMk_space him)
    refine hpair.congr_of_eventuallyEq ?_ ?_
    · filter_upwards [he] with y hy
      ext <;> simp [trivializationAt_complexification, Trivialization.complexification_apply,
        Trivialization.linearMapAt_apply, hy]
    · ext <;> simp [trivializationAt_complexification, Trivialization.complexification_apply,
        Trivialization.linearMapAt_apply, hx₀]

/-- Pointwise version of `contMDiffWithinAt_complexification_totalSpace_iff`. -/
theorem contMDiffAt_complexification_totalSpace_iff
    {f : M → TotalSpace (Complexification F) fun x ↦ ℂ ⊗[ℝ] E x} {x₀ : M} :
    ContMDiffAt IM (IB.prod 𝓘(ℝ, Complexification F)) n f x₀ ↔
      ContMDiffAt IM (IB.prod 𝓘(ℝ, F)) n
        (fun y ↦ (⟨(f y).proj, realPart (E (f y).proj) (f y).2⟩ : TotalSpace F E)) x₀ ∧
      ContMDiffAt IM (IB.prod 𝓘(ℝ, F)) n
        (fun y ↦ (⟨(f y).proj, imaginaryPart (E (f y).proj) (f y).2⟩ : TotalSpace F E)) x₀ := by
  simp_rw [← contMDiffWithinAt_univ]
  exact contMDiffWithinAt_complexification_totalSpace_iff

/-- Domain version of `contMDiffWithinAt_complexification_totalSpace_iff`. -/
theorem contMDiffOn_complexification_totalSpace_iff
    {f : M → TotalSpace (Complexification F) fun x ↦ ℂ ⊗[ℝ] E x} {s : Set M} :
    ContMDiffOn IM (IB.prod 𝓘(ℝ, Complexification F)) n f s ↔
      ContMDiffOn IM (IB.prod 𝓘(ℝ, F)) n
        (fun y ↦ (⟨(f y).proj, realPart (E (f y).proj) (f y).2⟩ : TotalSpace F E)) s ∧
      ContMDiffOn IM (IB.prod 𝓘(ℝ, F)) n
        (fun y ↦ (⟨(f y).proj, imaginaryPart (E (f y).proj) (f y).2⟩ : TotalSpace F E)) s := by
  simp only [ContMDiffOn, contMDiffWithinAt_complexification_totalSpace_iff, forall_and]

/-- Global version of `contMDiffWithinAt_complexification_totalSpace_iff`. -/
theorem contMDiff_complexification_totalSpace_iff
    {f : M → TotalSpace (Complexification F) fun x ↦ ℂ ⊗[ℝ] E x} :
    ContMDiff IM (IB.prod 𝓘(ℝ, Complexification F)) n f ↔
      ContMDiff IM (IB.prod 𝓘(ℝ, F)) n
        (fun y ↦ (⟨(f y).proj, realPart (E (f y).proj) (f y).2⟩ : TotalSpace F E)) ∧
      ContMDiff IM (IB.prod 𝓘(ℝ, F)) n
        (fun y ↦ (⟨(f y).proj, imaginaryPart (E (f y).proj) (f y).2⟩ : TotalSpace F E)) := by
  simp only [ContMDiff, contMDiffAt_complexification_totalSpace_iff, forall_and]

/-- A section `s : ∀ x, ℂ ⊗[ℝ] E x` is `C^n` within `u` at `x₀` if and only if its real and
imaginary parts `fun x ↦ realPart (E x) (s x)` and `fun x ↦ imaginaryPart (E x) (s x)` are `C^n`
sections of `E` within `u` at `x₀`. -/
theorem contMDiffWithinAt_complexification_section_iff
    {s : ∀ x, ℂ ⊗[ℝ] E x} {u : Set B} {x₀ : B} :
    ContMDiffWithinAt IB (IB.prod 𝓘(ℝ, Complexification F)) n
        (fun x ↦ TotalSpace.mk' (Complexification F) x (s x)) u x₀ ↔
      ContMDiffWithinAt IB (IB.prod 𝓘(ℝ, F)) n (T% fun x ↦ realPart (E x) (s x)) u x₀ ∧
      ContMDiffWithinAt IB (IB.prod 𝓘(ℝ, F)) n (T% fun x ↦ imaginaryPart (E x) (s x)) u x₀ :=
  contMDiffWithinAt_complexification_totalSpace_iff

/-- Pointwise version of `contMDiffWithinAt_complexification_section_iff`. -/
theorem contMDiffAt_complexification_section_iff
    {s : ∀ x, ℂ ⊗[ℝ] E x} {x₀ : B} :
    ContMDiffAt IB (IB.prod 𝓘(ℝ, Complexification F)) n
        (fun x ↦ TotalSpace.mk' (Complexification F) x (s x)) x₀ ↔
      ContMDiffAt IB (IB.prod 𝓘(ℝ, F)) n (T% fun x ↦ realPart (E x) (s x)) x₀ ∧
      ContMDiffAt IB (IB.prod 𝓘(ℝ, F)) n (T% fun x ↦ imaginaryPart (E x) (s x)) x₀ :=
  contMDiffAt_complexification_totalSpace_iff

/-- Domain version of `contMDiffWithinAt_complexification_section_iff`. -/
theorem contMDiffOn_complexification_section_iff
    {s : ∀ x, ℂ ⊗[ℝ] E x} {u : Set B} :
    ContMDiffOn IB (IB.prod 𝓘(ℝ, Complexification F)) n
        (fun x ↦ TotalSpace.mk' (Complexification F) x (s x)) u ↔
      ContMDiffOn IB (IB.prod 𝓘(ℝ, F)) n (T% fun x ↦ realPart (E x) (s x)) u ∧
      ContMDiffOn IB (IB.prod 𝓘(ℝ, F)) n (T% fun x ↦ imaginaryPart (E x) (s x)) u :=
  contMDiffOn_complexification_totalSpace_iff

/-- Global version of `contMDiffWithinAt_complexification_section_iff`. -/
theorem contMDiff_complexification_section_iff
    {s : ∀ x, ℂ ⊗[ℝ] E x} :
    ContMDiff IB (IB.prod 𝓘(ℝ, Complexification F)) n
        (fun x ↦ TotalSpace.mk' (Complexification F) x (s x)) ↔
      ContMDiff IB (IB.prod 𝓘(ℝ, F)) n (T% fun x ↦ realPart (E x) (s x)) ∧
      ContMDiff IB (IB.prod 𝓘(ℝ, F)) n (T% fun x ↦ imaginaryPart (E x) (s x)) :=
  contMDiff_complexification_totalSpace_iff

end RegularityCharacterization

section TotalSpaceDiffeomorphs

variable (IB F n E)

/-- Fibrewise complex conjugation `z ⊗ₜ v ↦ conj z ⊗ₜ v` as an involutive `C^n` diffeomorphism of
the total space of `fun x ↦ ℂ ⊗[ℝ] E x`, requiring neither `ContMDiffVectorBundle` nor finite rank
nor fibrewise topological-group hypotheses. -/
def tmulConjDiffeomorph :
    TotalSpace (Complexification F) (fun x ↦ ℂ ⊗[ℝ] E x) ≃ₘ^n⟮
      IB.prod 𝓘(ℝ, Complexification F), IB.prod 𝓘(ℝ, Complexification F)⟯
      TotalSpace (Complexification F) (fun x ↦ ℂ ⊗[ℝ] E x) where
  toFun p := ⟨p.proj, tmulConj (E p.proj) p.2⟩
  invFun p := ⟨p.proj, tmulConj (E p.proj) p.2⟩
  left_inv := fun ⟨x, u⟩ ↦ congrArg (TotalSpace.mk x) (tmulConj_tmulConj (E x) u)
  right_inv := fun ⟨x, u⟩ ↦ congrArg (TotalSpace.mk x) (tmulConj_tmulConj (E x) u)
  contMDiff_toFun := by
    obtain ⟨hre, him⟩ := (contMDiff_complexification_totalSpace_iff (F := F) (E := E)).mp
      (contMDiff_id (I := IB.prod 𝓘(ℝ, Complexification F)) (n := n))
    refine (contMDiff_complexification_totalSpace_iff (F := F) (E := E)).mpr
      ⟨by simpa using hre, ?_⟩
    simpa [neg_one_smul] using (contMDiff_const (c := (-1 : ℝ))).smul_totalSpace him
  contMDiff_invFun := by
    obtain ⟨hre, him⟩ := (contMDiff_complexification_totalSpace_iff (F := F) (E := E)).mp
      (contMDiff_id (I := IB.prod 𝓘(ℝ, Complexification F)) (n := n))
    refine (contMDiff_complexification_totalSpace_iff (F := F) (E := E)).mpr
      ⟨by simpa using hre, ?_⟩
    simpa [neg_one_smul] using (contMDiff_const (c := (-1 : ℝ))).smul_totalSpace him

/-- The real/imaginary-part `C^n` diffeomorphism between the total space of the complexified bundle
`fun x ↦ ℂ ⊗[ℝ] E x` and the total space of the direct-sum bundle `E ×ᵇ E`. -/
def complexificationTotalSpaceDiffeomorphProd :
    TotalSpace (Complexification F) (fun x ↦ ℂ ⊗[ℝ] E x) ≃ₘ^n⟮
      IB.prod 𝓘(ℝ, Complexification F), IB.prod 𝓘(ℝ, F × F)⟯
      TotalSpace (F × F) (E ×ᵇ E) where
  toFun p := ⟨p.proj, complexificationEquivProd (E p.proj) p.2⟩
  invFun p := ⟨p.proj, (complexificationEquivProd (E p.proj)).symm p.2⟩
  left_inv := fun ⟨x, u⟩ ↦
    congrArg (TotalSpace.mk x) ((complexificationEquivProd (E x)).symm_apply_apply u)
  right_inv := fun ⟨x, v⟩ ↦
    congrArg (TotalSpace.mk x) ((complexificationEquivProd (E x)).apply_symm_apply v)
  contMDiff_toFun := by
    rw [Equiv.coe_fn_mk]
    intro p₀
    obtain ⟨hb, hp₀⟩ := Bundle.contMDiffAt_totalSpace.mp
      (contMDiffAt_id (I := IB.prod 𝓘(ℝ, Complexification F)) (n := n) (x := p₀))
    refine Bundle.contMDiffAt_totalSpace.mpr ⟨hb, ?_⟩
    refine (((Complexification.equivProd F : Complexification F →L[ℝ] F × F).contDiff
      (n := n)).comp_contMDiffAt hp₀).congr_of_eventuallyEq ?_
    have hx₀ : p₀.proj ∈ (trivializationAt F E p₀.proj).baseSet :=
      mem_baseSet_trivializationAt F E p₀.proj
    filter_upwards [hb.continuousAt.preimage_mem_nhds
      ((trivializationAt F E p₀.proj).open_baseSet.mem_nhds hx₀)] with p hp
    have hp' : p.proj ∈ (trivializationAt F E p₀.proj).baseSet := hp
    have hprod : trivializationAt (F × F) (E ×ᵇ E) p₀.proj =
        (trivializationAt F E p₀.proj).prod (trivializationAt F E p₀.proj) := rfl
    dsimp only [Function.comp_def, id_eq]
    rw [hprod, complexificationEquivProd_apply, Trivialization.prod_apply' ℝ hp' hp']
    simp [trivializationAt_complexification, Trivialization.complexification_apply,
      Trivialization.linearMapAt_apply, hp']
  contMDiff_invFun := by
    rw [Equiv.coe_fn_symm_mk]
    intro p₀
    obtain ⟨hb, hp₀⟩ := Bundle.contMDiffAt_totalSpace.mp
      (contMDiffAt_id (I := IB.prod 𝓘(ℝ, F × F)) (n := n) (x := p₀))
    refine Bundle.contMDiffAt_totalSpace.mpr ⟨hb, ?_⟩
    refine ((((Complexification.equivProd F).symm : F × F →L[ℝ] Complexification F).contDiff
      (n := n)).comp_contMDiffAt hp₀).congr_of_eventuallyEq ?_
    have hx₀ : p₀.proj ∈ (trivializationAt F E p₀.proj).baseSet :=
      mem_baseSet_trivializationAt F E p₀.proj
    filter_upwards [hb.continuousAt.preimage_mem_nhds
      ((trivializationAt F E p₀.proj).open_baseSet.mem_nhds hx₀)] with p hp
    rcases p with ⟨x, v₁, v₂⟩
    have hx : x ∈ (trivializationAt F E p₀.proj).baseSet := hp
    have hprod : trivializationAt (F × F) (E ×ᵇ E) p₀.proj =
        (trivializationAt F E p₀.proj).prod (trivializationAt F E p₀.proj) := rfl
    dsimp only [Function.comp_def, id_eq]
    rw [hprod, Trivialization.prod_apply' ℝ hx hx]
    ext <;> simp [trivializationAt_complexification, Trivialization.complexification_apply,
      Trivialization.linearMapAt_apply, hx]

variable {IB F n E}

@[simp]
theorem tmulConjDiffeomorph_apply
    (p : TotalSpace (Complexification F) fun x ↦ ℂ ⊗[ℝ] E x) :
    tmulConjDiffeomorph IB F n E p = ⟨p.proj, tmulConj (E p.proj) p.2⟩ := (rfl)

@[simp]
theorem tmulConjDiffeomorph_symm :
    (tmulConjDiffeomorph IB F n E).symm = tmulConjDiffeomorph IB F n E := (rfl)

@[simp]
theorem toHomeomorph_tmulConjDiffeomorph
    [∀ x, IsTopologicalAddGroup (E x)] [∀ x, ContinuousSMul ℝ (E x)] :
    (tmulConjDiffeomorph IB F n E).toHomeomorph = tmulConjHomeomorph F E :=
  Homeomorph.ext fun _ ↦ by simp

@[simp]
theorem complexificationTotalSpaceDiffeomorphProd_apply
    (p : TotalSpace (Complexification F) fun x ↦ ℂ ⊗[ℝ] E x) :
    complexificationTotalSpaceDiffeomorphProd IB F n E p =
      ⟨p.proj, (realPart (E p.proj) p.2, imaginaryPart (E p.proj) p.2)⟩ :=
  congrArg (TotalSpace.mk p.proj) (complexificationEquivProd_apply p.2)

@[simp]
theorem complexificationTotalSpaceDiffeomorphProd_symm_apply
    (p : TotalSpace (F × F) (E ×ᵇ E)) :
    (complexificationTotalSpaceDiffeomorphProd IB F n E).symm p =
      ⟨p.proj, 1 ⊗ₜ[ℝ] p.2.1 + Complex.I ⊗ₜ[ℝ] p.2.2⟩ :=
  congrArg (TotalSpace.mk p.proj) (complexificationEquivProd_symm_apply p.2)

theorem proj_complexificationTotalSpaceDiffeomorphProd
    (p : TotalSpace (Complexification F) fun x ↦ ℂ ⊗[ℝ] E x) :
    (complexificationTotalSpaceDiffeomorphProd IB F n E p).proj = p.proj := (rfl)

@[simp]
theorem toHomeomorph_complexificationTotalSpaceDiffeomorphProd
    [∀ x, IsTopologicalAddGroup (E x)] [∀ x, ContinuousSMul ℝ (E x)] :
    (complexificationTotalSpaceDiffeomorphProd IB F n E).toHomeomorph =
      complexificationTotalSpaceHomeomorphProd F E :=
  Homeomorph.ext fun _ ↦ by simp

end TotalSpaceDiffeomorphs

section HomBundleSections

variable [∀ x, IsTopologicalAddGroup (E x)] [∀ x, ContinuousSMul ℝ (E x)]

theorem contMDiff_realPartCLM_bundle :
    ContMDiff IB (IB.prod 𝓘(ℝ, Complexification F →L[ℝ] F)) n
      (fun x ↦ TotalSpace.mk' (Complexification F →L[ℝ] F)
        (E := fun y ↦ ℂ ⊗[ℝ] E y →L[ℝ] E y) x (realPartCLM (E x))) :=
  contMDiff_hom_bundle_of_inCoordinates_eq_const fun a _ _ hx ↦ inCoordinates_realPartCLM a hx

theorem contMDiff_imaginaryPartCLM_bundle :
    ContMDiff IB (IB.prod 𝓘(ℝ, Complexification F →L[ℝ] F)) n
      (fun x ↦ TotalSpace.mk' (Complexification F →L[ℝ] F)
        (E := fun y ↦ ℂ ⊗[ℝ] E y →L[ℝ] E y) x (imaginaryPartCLM (E x))) :=
  contMDiff_hom_bundle_of_inCoordinates_eq_const fun a _ _ hx ↦ inCoordinates_imaginaryPartCLM a hx

theorem contMDiff_oneTmulCLM_bundle :
    ContMDiff IB (IB.prod 𝓘(ℝ, F →L[ℝ] Complexification F)) n
      (fun x ↦ TotalSpace.mk' (F →L[ℝ] Complexification F)
        (E := fun y ↦ E y →L[ℝ] ℂ ⊗[ℝ] E y) x (oneTmulCLM (E x))) :=
  contMDiff_hom_bundle_of_inCoordinates_eq_const fun a _ hx _ ↦ inCoordinates_oneTmulCLM a hx

theorem contMDiff_ITmulCLM_bundle :
    ContMDiff IB (IB.prod 𝓘(ℝ, F →L[ℝ] Complexification F)) n
      (fun x ↦ TotalSpace.mk' (F →L[ℝ] Complexification F)
        (E := fun y ↦ E y →L[ℝ] ℂ ⊗[ℝ] E y) x (ITmulCLM (E x))) :=
  contMDiff_hom_bundle_of_inCoordinates_eq_const fun a _ hx _ ↦ inCoordinates_ITmulCLM a hx

theorem contMDiff_tmulConjCLM_bundle :
    ContMDiff IB (IB.prod 𝓘(ℝ, Complexification F →L[ℝ] Complexification F)) n
      (fun x ↦ TotalSpace.mk' (Complexification F →L[ℝ] Complexification F)
        (E := fun y ↦ ℂ ⊗[ℝ] E y →L[ℝ] ℂ ⊗[ℝ] E y) x (tmulConjCLM (E x))) :=
  contMDiff_hom_bundle_of_inCoordinates_eq_const fun a _ hx _ ↦
    inCoordinates_tmulConjCLM a (by rwa [baseSet_trivializationAt_complexification] at hx)

theorem contMDiff_complexificationEquivProd_bundle :
    ContMDiff IB (IB.prod 𝓘(ℝ, Complexification F →L[ℝ] F × F)) n
      (fun x ↦ TotalSpace.mk' (Complexification F →L[ℝ] F × F)
        (E := fun y ↦ ℂ ⊗[ℝ] E y →L[ℝ] (E ×ᵇ E) y) x
        (complexificationEquivProd (E x) : ℂ ⊗[ℝ] E x →L[ℝ] (E ×ᵇ E) x)) :=
  contMDiff_hom_bundle_of_inCoordinates_eq_const fun a _ hx _ ↦
    inCoordinates_complexificationEquivProd a
      (by rwa [baseSet_trivializationAt_complexification] at hx)

theorem contMDiff_complexificationEquivProd_symm_bundle :
    ContMDiff IB (IB.prod 𝓘(ℝ, (F × F) →L[ℝ] Complexification F)) n
      (fun x ↦ TotalSpace.mk' ((F × F) →L[ℝ] Complexification F)
        (E := fun y ↦ (E ×ᵇ E) y →L[ℝ] ℂ ⊗[ℝ] E y) x
        ((complexificationEquivProd (E x)).symm : (E ×ᵇ E) x →L[ℝ] ℂ ⊗[ℝ] E x)) :=
  contMDiff_hom_bundle_of_inCoordinates_eq_const fun a _ _ hx ↦
    inCoordinates_complexificationEquivProd_symm a
      (by rwa [baseSet_trivializationAt_complexification] at hx)

end HomBundleSections

end ComplexificationBundle

end TauCeti

/-! ### Global `C^n` sections of the complexified bundle -/

namespace ContMDiffSection

open TauCeti

section ComplexificationSections

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] (IB : ModelWithCorners ℝ EB HB)
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] (n : ℕ∞ω)
  (E : B → Type*) [∀ x, AddCommGroup (E x)] [∀ x, Module ℝ (E x)]
  [TopologicalSpace (TotalSpace F E)] [∀ x, TopologicalSpace (E x)]
  [FiberBundle F E] [VectorBundle ℝ F E]
  [∀ x, TopologicalSpace (ℂ ⊗[ℝ] E x)] [∀ x, IsComplexificationTopology (E x)]

/-- Fibrewise real part as an `ℝ`-linear map from `C^n` sections of `fun x ↦ ℂ ⊗[ℝ] E x` to `C^n`
sections of `E`. -/
def realPartLinearMap :
    Cₛ^n⟮IB; Complexification F, fun x ↦ ℂ ⊗[ℝ] E x⟯ →ₗ[ℝ] Cₛ^n⟮IB; F, E⟯ where
  toFun σ := ⟨fun x ↦ realPart (E x) (σ x),
    ((contMDiff_complexification_section_iff (F := F)).mp σ.contMDiff).1⟩
  map_add' σ τ := ext fun x ↦ map_add (realPart (E x)) (σ x) (τ x)
  map_smul' r σ := ext fun x ↦ map_smul (realPart (E x)) r (σ x)

variable {IB F n E} in
@[simp]
theorem realPartLinearMap_apply
    (σ : Cₛ^n⟮IB; Complexification F, fun x ↦ ℂ ⊗[ℝ] E x⟯) (x : B) :
    realPartLinearMap IB F n E σ x = realPart (E x) (σ x) := (rfl)

/-- Fibrewise imaginary part as an `ℝ`-linear map from `C^n` sections of `fun x ↦ ℂ ⊗[ℝ] E x` to
`C^n` sections of `E`. -/
def imaginaryPartLinearMap :
    Cₛ^n⟮IB; Complexification F, fun x ↦ ℂ ⊗[ℝ] E x⟯ →ₗ[ℝ] Cₛ^n⟮IB; F, E⟯ where
  toFun σ := ⟨fun x ↦ imaginaryPart (E x) (σ x),
    ((contMDiff_complexification_section_iff (F := F)).mp σ.contMDiff).2⟩
  map_add' σ τ := ext fun x ↦ map_add (imaginaryPart (E x)) (σ x) (τ x)
  map_smul' r σ := ext fun x ↦ map_smul (imaginaryPart (E x)) r (σ x)

variable {IB F n E} in
@[simp]
theorem imaginaryPartLinearMap_apply
    (σ : Cₛ^n⟮IB; Complexification F, fun x ↦ ℂ ⊗[ℝ] E x⟯) (x : B) :
    imaginaryPartLinearMap IB F n E σ x = imaginaryPart (E x) (σ x) := (rfl)

/-- Real inclusion `s ↦ (x ↦ 1 ⊗ₜ s x)` as an `ℝ`-linear map on `C^n` sections. -/
def oneTmulLinearMap :
    Cₛ^n⟮IB; F, E⟯ →ₗ[ℝ] Cₛ^n⟮IB; Complexification F, fun x ↦ ℂ ⊗[ℝ] E x⟯ where
  toFun s := ⟨fun x ↦ 1 ⊗ₜ[ℝ] s x, (contMDiff_complexification_section_iff (F := F)).mpr
    ⟨by simpa using s.contMDiff, by simpa using (0 : Cₛ^n⟮IB; F, E⟯).contMDiff⟩⟩
  map_add' s t := ext fun x ↦ TensorProduct.tmul_add 1 (s x) (t x)
  map_smul' r s := ext fun x ↦ TensorProduct.tmul_smul r (1 : ℂ) (s x)

variable {IB F n E} in
@[simp]
theorem oneTmulLinearMap_apply (s : Cₛ^n⟮IB; F, E⟯) (x : B) :
    oneTmulLinearMap IB F n E s x = 1 ⊗ₜ[ℝ] s x := (rfl)

/-- Imaginary inclusion `s ↦ (x ↦ I ⊗ₜ s x)` as an `ℝ`-linear map on `C^n` sections. -/
def ITmulLinearMap :
    Cₛ^n⟮IB; F, E⟯ →ₗ[ℝ] Cₛ^n⟮IB; Complexification F, fun x ↦ ℂ ⊗[ℝ] E x⟯ where
  toFun s := ⟨fun x ↦ Complex.I ⊗ₜ[ℝ] s x, (contMDiff_complexification_section_iff (F := F)).mpr
    ⟨by simpa using (0 : Cₛ^n⟮IB; F, E⟯).contMDiff, by simpa using s.contMDiff⟩⟩
  map_add' s t := ext fun x ↦ TensorProduct.tmul_add Complex.I (s x) (t x)
  map_smul' r s := ext fun x ↦ TensorProduct.tmul_smul r Complex.I (s x)

variable {IB F n E} in
@[simp]
theorem ITmulLinearMap_apply (s : Cₛ^n⟮IB; F, E⟯) (x : B) :
    ITmulLinearMap IB F n E s x = Complex.I ⊗ₜ[ℝ] s x := (rfl)

variable {IB F n E} in
theorem I_smul_oneTmulLinearMap (s : Cₛ^n⟮IB; F, E⟯) :
    Complex.I • oneTmulLinearMap IB F n E s = ITmulLinearMap IB F n E s :=
  ext fun x ↦ by simp [Complex.I, TensorProduct.smul_tmul']

/-- Fibrewise complex conjugation `z ⊗ₜ v ↦ conj z ⊗ₜ v` as a conjugate-linear equivalence on
`C^n` sections of `fun x ↦ ℂ ⊗[ℝ] E x`. -/
def conjEquiv :
    Cₛ^n⟮IB; Complexification F, fun x ↦ ℂ ⊗[ℝ] E x⟯ ≃ₗ⋆[ℂ]
      Cₛ^n⟮IB; Complexification F, fun x ↦ ℂ ⊗[ℝ] E x⟯ where
  toFun σ := ⟨fun x ↦ tmulConj (E x) (σ x), (contMDiff_complexification_section_iff (F := F)).mpr
    ⟨by simpa using ((contMDiff_complexification_section_iff (F := F)).mp σ.contMDiff).1,
     by simpa using
       ((contMDiff_complexification_section_iff (F := F)).mp σ.contMDiff).2.neg_section⟩⟩
  invFun σ := ⟨fun x ↦ tmulConj (E x) (σ x), (contMDiff_complexification_section_iff (F := F)).mpr
    ⟨by simpa using ((contMDiff_complexification_section_iff (F := F)).mp σ.contMDiff).1,
     by simpa using
       ((contMDiff_complexification_section_iff (F := F)).mp σ.contMDiff).2.neg_section⟩⟩
  map_add' σ τ := ext fun x ↦ map_add (tmulConj (E x)) (σ x) (τ x)
  map_smul' c σ := ext fun x ↦ map_smulₛₗ (tmulConj (E x)) c (σ x)
  left_inv σ := ext fun x ↦ tmulConj_tmulConj (E x) (σ x)
  right_inv σ := ext fun x ↦ tmulConj_tmulConj (E x) (σ x)

variable {IB F n E} in
@[simp]
theorem conjEquiv_apply
    (σ : Cₛ^n⟮IB; Complexification F, fun x ↦ ℂ ⊗[ℝ] E x⟯) (x : B) :
    conjEquiv IB F n E σ x = tmulConj (E x) (σ x) := (rfl)

variable {IB F n E} in
@[simp]
theorem conjEquiv_symm :
    (conjEquiv IB F n E).symm = conjEquiv IB F n E := (rfl)

/-- Real-linear isomorphism between `C^n` sections of `fun x ↦ ℂ ⊗[ℝ] E x` and pairs of `C^n`
sections of `E`, given by `(realPartLinearMap, imaginaryPartLinearMap)`. -/
def complexificationEquivProd :
    Cₛ^n⟮IB; Complexification F, fun x ↦ ℂ ⊗[ℝ] E x⟯ ≃ₗ[ℝ]
      Cₛ^n⟮IB; F, E⟯ × Cₛ^n⟮IB; F, E⟯ where
  toFun σ := (realPartLinearMap IB F n E σ, imaginaryPartLinearMap IB F n E σ)
  map_add' σ τ := Prod.ext (map_add _ σ τ) (map_add _ σ τ)
  map_smul' r σ := Prod.ext (map_smul _ r σ) (map_smul _ r σ)
  invFun p := oneTmulLinearMap IB F n E p.1 + ITmulLinearMap IB F n E p.2
  left_inv σ := ext fun x ↦ by simp
  right_inv := fun ⟨s, t⟩ ↦ Prod.ext (ext fun x ↦ by simp) (ext fun x ↦ by simp)

/-- The canonical `ℂ`-linear isomorphism
`ℂ ⊗[ℝ] Cₛ^n⟮IB; F, E⟯ ≃ₗ[ℂ] Cₛ^n⟮IB; Complexification F, fun x ↦ ℂ ⊗[ℝ] E x⟯` sending a pure
tensor `z ⊗ₜ s` to the `C^n` section `x ↦ z ⊗ₜ s x` and decomposing any `C^n` section `σ` of
`fun x ↦ ℂ ⊗[ℝ] E x` as `1 ⊗ₜ Re σ + I ⊗ₜ Im σ`. -/
def complexificationEquiv :
    ℂ ⊗[ℝ] Cₛ^n⟮IB; F, E⟯ ≃ₗ[ℂ]
      Cₛ^n⟮IB; Complexification F, fun x ↦ ℂ ⊗[ℝ] E x⟯ where
  toFun u :=
    oneTmulLinearMap IB F n E (realPart Cₛ^n⟮IB; F, E⟯ u) +
      ITmulLinearMap IB F n E (imaginaryPart Cₛ^n⟮IB; F, E⟯ u)
  map_add' u v := by
    simp only [map_add]
    abel
  map_smul' c u := ext fun x ↦ by
    simpa [smul_add, TensorProduct.tmul_sub, TensorProduct.tmul_add,
      TensorProduct.tmul_smul] using (smul_one_tmul_add_I_tmul (E x) c
        (realPart Cₛ^n⟮IB; F, E⟯ u x) (imaginaryPart Cₛ^n⟮IB; F, E⟯ u x)).symm
  invFun σ :=
    1 ⊗ₜ[ℝ] realPartLinearMap IB F n E σ + Complex.I ⊗ₜ[ℝ] imaginaryPartLinearMap IB F n E σ
  left_inv u := by
    dsimp only
    have hre : realPartLinearMap IB F n E
        (oneTmulLinearMap IB F n E (realPart Cₛ^n⟮IB; F, E⟯ u) +
          ITmulLinearMap IB F n E (imaginaryPart Cₛ^n⟮IB; F, E⟯ u)) =
        realPart Cₛ^n⟮IB; F, E⟯ u :=
      ext fun x ↦ by simp
    have him : imaginaryPartLinearMap IB F n E
        (oneTmulLinearMap IB F n E (realPart Cₛ^n⟮IB; F, E⟯ u) +
          ITmulLinearMap IB F n E (imaginaryPart Cₛ^n⟮IB; F, E⟯ u)) =
        imaginaryPart Cₛ^n⟮IB; F, E⟯ u :=
      ext fun x ↦ by simp
    rw [hre, him, one_tmul_realPart_add_I_tmul_imaginaryPart]
  right_inv σ := ext fun x ↦ by simp

variable {IB F n E}

@[simp]
theorem complexificationEquivProd_apply
    (σ : Cₛ^n⟮IB; Complexification F, fun x ↦ ℂ ⊗[ℝ] E x⟯) :
    complexificationEquivProd IB F n E σ =
      (realPartLinearMap IB F n E σ, imaginaryPartLinearMap IB F n E σ) := (rfl)

@[simp]
theorem complexificationEquivProd_symm_apply
    (p : Cₛ^n⟮IB; F, E⟯ × Cₛ^n⟮IB; F, E⟯) :
    (complexificationEquivProd IB F n E).symm p =
      oneTmulLinearMap IB F n E p.1 + ITmulLinearMap IB F n E p.2 := (rfl)

@[simp]
theorem complexificationEquiv_tmul (z : ℂ) (s : Cₛ^n⟮IB; F, E⟯) (x : B) :
    complexificationEquiv IB F n E (z ⊗ₜ[ℝ] s) x = z ⊗ₜ[ℝ] s x := by
  simp only [complexificationEquiv, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk,
    coe_add, Pi.add_apply, oneTmulLinearMap_apply, ITmulLinearMap_apply, realPart_tmul,
    imaginaryPart_tmul, coe_smul, Pi.smul_apply]
  rw [← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul, ← TensorProduct.add_tmul]
  simp [Complex.real_smul]

theorem complexificationEquiv_tmul_eq_smul (z : ℂ) (s : Cₛ^n⟮IB; F, E⟯) :
    complexificationEquiv IB F n E (z ⊗ₜ[ℝ] s) = z • oneTmulLinearMap IB F n E s :=
  ext fun x ↦ by simp [TensorProduct.smul_tmul']

@[simp]
theorem complexificationEquiv_symm_apply
    (σ : Cₛ^n⟮IB; Complexification F, fun x ↦ ℂ ⊗[ℝ] E x⟯) :
    (complexificationEquiv IB F n E).symm σ =
      1 ⊗ₜ[ℝ] realPartLinearMap IB F n E σ +
        Complex.I ⊗ₜ[ℝ] imaginaryPartLinearMap IB F n E σ := (rfl)

@[simp]
theorem realPartLinearMap_complexificationEquiv (u : ℂ ⊗[ℝ] Cₛ^n⟮IB; F, E⟯) :
    realPartLinearMap IB F n E (complexificationEquiv IB F n E u) =
      realPart Cₛ^n⟮IB; F, E⟯ u :=
  ext fun x ↦ by simp [complexificationEquiv]

@[simp]
theorem imaginaryPartLinearMap_complexificationEquiv (u : ℂ ⊗[ℝ] Cₛ^n⟮IB; F, E⟯) :
    imaginaryPartLinearMap IB F n E (complexificationEquiv IB F n E u) =
      imaginaryPart Cₛ^n⟮IB; F, E⟯ u :=
  ext fun x ↦ by simp [complexificationEquiv]

@[simp]
theorem realPart_complexificationEquiv_apply (u : ℂ ⊗[ℝ] Cₛ^n⟮IB; F, E⟯) (x : B) :
    realPart (E x) (complexificationEquiv IB F n E u x) = realPart Cₛ^n⟮IB; F, E⟯ u x := by
  rw [← realPartLinearMap_apply, realPartLinearMap_complexificationEquiv]

@[simp]
theorem imaginaryPart_complexificationEquiv_apply (u : ℂ ⊗[ℝ] Cₛ^n⟮IB; F, E⟯) (x : B) :
    imaginaryPart (E x) (complexificationEquiv IB F n E u x) =
      imaginaryPart Cₛ^n⟮IB; F, E⟯ u x := by
  rw [← imaginaryPartLinearMap_apply, imaginaryPartLinearMap_complexificationEquiv]

@[simp]
theorem conjEquiv_complexificationEquiv (u : ℂ ⊗[ℝ] Cₛ^n⟮IB; F, E⟯) :
    conjEquiv IB F n E (complexificationEquiv IB F n E u) =
      complexificationEquiv IB F n E (tmulConj Cₛ^n⟮IB; F, E⟯ u) := by
  obtain ⟨s, t, rfl⟩ := exists_one_tmul_add_I_tmul u
  ext x
  simp [TensorProduct.neg_tmul]

end ComplexificationSections

end ContMDiffSection

end
