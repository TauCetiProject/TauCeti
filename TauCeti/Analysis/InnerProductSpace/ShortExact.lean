/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.ContinuousInverse
public import Mathlib.Topology.Algebra.Module.Equiv.Prod
public import TauCeti.Analysis.InnerProductSpace.OrthogonalSplitting
public import TauCeti.Analysis.InnerProductSpace.Projection.Basic
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Exact

/-!
# Topological splittings of short exact sequences through Hilbert spaces

When the ambient space is a Hilbert space over an `RCLike` field, the Banach open mapping theorem
combined with orthogonal projection upgrades algebraic injectivity (with closed range) and
algebraic surjectivity to canonical continuous linear one-sided inverses:

* `ContinuousLinearMap.orthogonalLeftInverse`: for an injective bounded map `f : E →L[𝕜] H` from a
  Banach space into a Hilbert space with closed range, the composite
  `(f.equivRange _ _)⁻¹ ∘ P_{im f}` is the unique continuous linear left inverse of `f` vanishing
  on `(range f)ᗮ` (`ContinuousLinearMap.eq_orthogonalLeftInverse`).
* `ContinuousLinearMap.orthogonalRightInverse (ContinuousLinearMap.id 𝕜 H) g`: for a surjective
  bounded map `g : H →L[𝕜] F` from a Hilbert space onto a Banach space, inverting the bijection
  `g|_{(ker g)ᗮ} : (ker g)ᗮ → F` gives the unique continuous linear right inverse of `g` with range
  in `(ker g)ᗮ` (`ContinuousLinearMap.eq_orthogonalRightInverse`).

Combined with `Function.Exact.isClosed_range`, every algebraically short exact sequence
`0 → E₁ --f--> H₂ --g--> E₃ → 0` of bounded linear maps with `E₁, E₃` Banach spaces and `H₂` a
Hilbert space splits topologically: `f` admits its orthogonal left inverse `ρ`, `g` admits its
orthogonal right inverse `σ = ContinuousLinearMap.orthogonalRightInverse (.id 𝕜 H₂) g`, and
`f.coprod σ` is a continuous linear equivalence `E₁ × E₃ ≃L[𝕜] H₂` with inverse `ρ.prod g`
(`TauCeti.orthogonalShortExactEquiv`).

## References

* N. Bourbaki, *Topological Vector Spaces*, Chapter V (*Hilbert Spaces*), §1, no. 5–6.
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §19.1.
-/

public section

namespace ContinuousLinearMap

section OrthogonalInverses

open scoped InnerProductSpace

variable {𝕜 E H F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

section LeftInverse
variable (f : E →L[𝕜] H) (hf : Function.Injective f) (hclo : IsClosed (f.range : Set H))

/-- The **orthogonal left inverse** of an injective continuous linear map `f : E →L[𝕜] H` from a
Banach space into a Hilbert space with closed range: project `H` orthogonally onto `range f` and
apply the Banach bounded inverse `(f.equivRange _ _)⁻¹`. -/
noncomputable def orthogonalLeftInverse : H →L[𝕜] E :=
  have : CompleteSpace f.range := hclo.completeSpace_coe
  (f.equivRange hf
    (by simpa only [LinearMap.coe_range, coe_coe] using hclo)).symm.toContinuousLinearMap ∘L
    f.range.orthogonalProjectionOnto

/-- Defining equation for `f.orthogonalLeftInverse`. -/
theorem orthogonalLeftInverse_def :
    let : CompleteSpace f.range := hclo.completeSpace_coe
    f.orthogonalLeftInverse hf hclo =
      (f.equivRange hf
        (by simpa only [LinearMap.coe_range, coe_coe] using hclo)).symm.toContinuousLinearMap ∘L
        f.range.orthogonalProjectionOnto := by
  rw [orthogonalLeftInverse]

/-- Evaluation formula for `f.orthogonalLeftInverse`: project `y` orthogonally onto `range f`
and apply the inverse of `f.equivRange`. -/
theorem orthogonalLeftInverse_apply (y : H) :
    let : CompleteSpace f.range := hclo.completeSpace_coe
    f.orthogonalLeftInverse hf hclo y =
      (f.equivRange hf (by simpa only [LinearMap.coe_range, coe_coe] using hclo)).symm
        (f.range.orthogonalProjectionOnto y) := by
  simp only [orthogonalLeftInverse, comp_apply, ContinuousLinearEquiv.coe_coe]

/-- `f.orthogonalLeftInverse` is a left inverse of `f`. -/
theorem leftInverse_orthogonalLeftInverse :
    Function.LeftInverse (f.orthogonalLeftInverse hf hclo) f := fun x ↦ by
  have : CompleteSpace f.range := hclo.completeSpace_coe
  have hclo' : IsClosed (Set.range f) := by simpa only [LinearMap.coe_range, coe_coe] using hclo
  have hproj : (f.range.orthogonalProjectionOnto (f x) : H) = f x := by
    rw [← Submodule.starProjection_apply]
    exact Submodule.starProjection_eq_self_iff.2 (LinearMap.mem_range_self _ x)
  have he : ((f.equivRange hf hclo' x : f.range) : H) = f x :=
    congrArg Subtype.val (DFunLike.congr_fun (f.coe_linearMap_equivRange hf hclo') x)
  simp [orthogonalLeftInverse, ContinuousLinearEquiv.symm_apply_eq, Subtype.ext_iff, hproj, he]

@[simp] theorem orthogonalLeftInverse_apply_self (x : E) :
    f.orthogonalLeftInverse hf hclo (f x) = x :=
  f.leftInverse_orthogonalLeftInverse hf hclo x

@[simp] theorem orthogonalLeftInverse_comp_self :
    f.orthogonalLeftInverse hf hclo ∘L f = ContinuousLinearMap.id 𝕜 E :=
  ContinuousLinearMap.ext (f.leftInverse_orthogonalLeftInverse hf hclo)

/-- Composing `f` on the left of its orthogonal left inverse recovers the orthogonal projection
onto `range f`. -/
@[simp] theorem self_comp_orthogonalLeftInverse :
    let : CompleteSpace f.range := hclo.completeSpace_coe
    f ∘L f.orthogonalLeftInverse hf hclo = f.range.starProjection := by
  have hclo' : IsClosed (Set.range f) := by simpa only [LinearMap.coe_range, coe_coe] using hclo
  ext y
  set u := (f.equivRange hf hclo').symm (f.range.orthogonalProjectionOnto y)
  have hu : ((f.equivRange hf hclo' u : f.range) : H) = f u :=
    congrArg Subtype.val (DFunLike.congr_fun (f.coe_linearMap_equivRange hf hclo') u)
  have hy : ((f.equivRange hf hclo' u : f.range) : H) = (f.range.orthogonalProjectionOnto y : H) :=
    congrArg Subtype.val ((f.equivRange hf hclo').apply_symm_apply _)
  rw [hu] at hy
  simpa only [orthogonalLeftInverse, comp_apply, ContinuousLinearEquiv.coe_coe,
    Submodule.starProjection_apply] using hy

/-- The kernel of `f.orthogonalLeftInverse` is `(range f)ᗮ`. -/
@[simp] theorem ker_orthogonalLeftInverse :
    (f.orthogonalLeftInverse hf hclo).ker = f.rangeᗮ := by
  have : CompleteSpace f.range := hclo.completeSpace_coe
  rw [orthogonalLeftInverse, toLinearMap_comp,
    ContinuousLinearEquiv.toLinearMap_toContinuousLinearMap, LinearEquiv.ker_comp]
  exact Submodule.ker_orthogonalProjectionOnto

/-- `f.orthogonalLeftInverse` is surjective, so its range is `⊤`. -/
@[simp] theorem range_orthogonalLeftInverse : (f.orthogonalLeftInverse hf hclo).range = ⊤ :=
  LinearMap.range_eq_top.2 (f.leftInverse_orthogonalLeftInverse hf hclo).surjective

/-- **Uniqueness of `orthogonalLeftInverse`.** Any continuous linear left inverse of `f` that
vanishes on `(range f)ᗮ` equals `f.orthogonalLeftInverse hf hclo`. -/
theorem eq_orthogonalLeftInverse {L : H →L[𝕜] E}
    (hL : L ∘L f = ContinuousLinearMap.id 𝕜 E) (hker : f.rangeᗮ ≤ L.ker) :
    L = f.orthogonalLeftInverse hf hclo := by
  have : CompleteSpace f.range := hclo.completeSpace_coe
  ext y
  have hsub : y - f (f.orthogonalLeftInverse hf hclo y) ∈ f.rangeᗮ := by
    rw [← comp_apply f, f.self_comp_orthogonalLeftInverse hf hclo]
    exact f.range.sub_starProjection_mem_orthogonal y
  have h0 := hker hsub
  rw [LinearMap.mem_ker, coe_coe, map_sub, sub_eq_zero, ← comp_apply L f, hL, id_apply] at h0
  exact h0

end LeftInverse

/-- An injective continuous linear map from a Banach space into a Hilbert space with closed range
has a continuous linear left inverse. Unlike
`ContinuousLinearMap.HasLeftInverse.of_injective_of_isClosed_range_of_closedComplement_range`, no
closed-complement hypothesis is needed because `H` is a Hilbert space. -/
theorem HasLeftInverse.of_injective_of_isClosed_range_of_innerProductSpace {f : E →L[𝕜] H}
    (hf : Function.Injective f) (hclo : IsClosed (f.range : Set H)) : f.HasLeftInverse :=
  ⟨f.orthogonalLeftInverse hf hclo, f.leftInverse_orthogonalLeftInverse hf hclo⟩

/-- In an exact sequence `0 → E --f--> H` followed by `H --q--> G`, with `E` a Banach space, `H` a
Hilbert space, and `G` a `T₁` topological module, `f` admits a continuous linear left inverse. -/
theorem HasLeftInverse.of_injective_of_exact_of_innerProductSpace {G : Type*} [TopologicalSpace G]
    [AddCommMonoid G] [Module 𝕜 G] [T1Space G] {f : E →L[𝕜] H} {q : H →L[𝕜] G}
    (hf : Function.Injective f) (hfq : Function.Exact f q) : f.HasLeftInverse :=
  .of_injective_of_isClosed_range_of_innerProductSpace hf hfq.isClosed_range

section RightInverse
variable (g : H →L[𝕜] F)

omit [CompleteSpace F] in
private theorem range_comp_subtypeL_orthogonal_eq_top (hg : Function.Surjective g) :
    (g ∘L g.kerᗮ.subtypeL).range = ⊤ :=
  have : CompleteSpace g.ker := g.isClosed_ker.completeSpace_coe
  g.range_comp_subtypeL_orthogonal.trans (LinearMap.range_eq_top.2 hg)

private noncomputable def restrictOrthogonalEquiv (hg : Function.Surjective g) : g.kerᗮ ≃L[𝕜] F :=
  ContinuousLinearEquiv.ofBijective (g ∘L g.kerᗮ.subtypeL) g.ker_comp_subtypeL_orthogonal
    (range_comp_subtypeL_orthogonal_eq_top g hg)

private noncomputable def rightInverseCandidate (hg : Function.Surjective g) : F →L[𝕜] H :=
  g.kerᗮ.subtypeL ∘L (restrictOrthogonalEquiv g hg).symm.toContinuousLinearMap

private theorem isOrthogonalRightInverse_rightInverseCandidate (hg : Function.Surjective g) :
    IsOrthogonalRightInverse (ContinuousLinearMap.id 𝕜 H) g
      (rightInverseCandidate g hg) where
  rightInverse y := by
    rw [rightInverseCandidate, comp_apply, ContinuousLinearEquiv.coe_coe,
      ← comp_apply g g.kerᗮ.subtypeL]
    exact (restrictOrthogonalEquiv g hg).apply_symm_apply y
  inner_eq_zero y k hk := by
    dsimp only [ContinuousLinearMap.id_apply]
    exact Submodule.inner_left_of_mem_orthogonal hk (Submodule.coe_mem _)

/-- For a surjective continuous linear map `g : H →L[𝕜] F` from a Hilbert space onto a Banach
space, `ContinuousLinearMap.orthogonalRightInverse (.id 𝕜 H) g` is a right inverse of `g` taking
values in `(ker g)ᗮ`. -/
theorem isOrthogonalRightInverse_orthogonalRightInverse (hg : Function.Surjective g) :
    IsOrthogonalRightInverse (ContinuousLinearMap.id 𝕜 H) g
      (orthogonalRightInverse (ContinuousLinearMap.id 𝕜 H) g) :=
  (isOrthogonalRightInverse_rightInverseCandidate g
    hg).isOrthogonalRightInverse_orthogonalRightInverse

private theorem rightInverseCandidate_eq_orthogonalRightInverse (hg : Function.Surjective g) :
    rightInverseCandidate g hg = orthogonalRightInverse (ContinuousLinearMap.id 𝕜 H) g :=
  (isOrthogonalRightInverse_rightInverseCandidate g hg).eq_orthogonalRightInverse
    Function.injective_id

/-- `orthogonalRightInverse (.id 𝕜 H) g` is a right inverse of `g`. -/
theorem rightInverse_orthogonalRightInverse (hg : Function.Surjective g) :
    Function.RightInverse (orthogonalRightInverse (ContinuousLinearMap.id 𝕜 H) g) g :=
  (g.isOrthogonalRightInverse_orthogonalRightInverse hg).rightInverse

@[simp] theorem apply_orthogonalRightInverse (hg : Function.Surjective g) (y : F) :
    g (orthogonalRightInverse (ContinuousLinearMap.id 𝕜 H) g y) = y :=
  g.rightInverse_orthogonalRightInverse hg y

@[simp] theorem self_comp_orthogonalRightInverse (hg : Function.Surjective g) :
    g ∘L orthogonalRightInverse (ContinuousLinearMap.id 𝕜 H) g = ContinuousLinearMap.id 𝕜 F :=
  ContinuousLinearMap.ext (g.rightInverse_orthogonalRightInverse hg)

/-- Composing `orthogonalRightInverse (.id 𝕜 H) g` on the left of `g` recovers the orthogonal
projection onto `(ker g)ᗮ`. -/
@[simp] theorem orthogonalRightInverse_comp_self (hg : Function.Surjective g) :
    orthogonalRightInverse (ContinuousLinearMap.id 𝕜 H) g ∘L g = g.kerᗮ.starProjection := by
  have : CompleteSpace g.ker := g.isClosed_ker.completeSpace_coe
  rw [← rightInverseCandidate_eq_orthogonalRightInverse g hg]
  set e := restrictOrthogonalEquiv g hg
  ext x
  have hx : e (g.kerᗮ.orthogonalProjectionOnto x) = g x := by
    simp only [e, restrictOrthogonalEquiv, ContinuousLinearEquiv.coeFn_ofBijective, comp_apply,
      Submodule.subtypeL_apply, Submodule.coe_orthogonalProjectionOnto_apply]
    exact DFunLike.congr_fun g.comp_starProjection_orthogonal_ker x
  have hsymm : e.symm (g x) = g.kerᗮ.orthogonalProjectionOnto x :=
    e.injective (by rw [e.apply_symm_apply, hx])
  simpa only [rightInverseCandidate, comp_apply, Submodule.subtypeL_apply,
    ContinuousLinearEquiv.coe_coe, Submodule.starProjection_apply] using
    congrArg Subtype.val hsymm

/-- `orthogonalRightInverse (.id 𝕜 H) g` is injective, so its kernel is `⊥`. -/
@[simp] theorem ker_orthogonalRightInverse (hg : Function.Surjective g) :
    (orthogonalRightInverse (ContinuousLinearMap.id 𝕜 H) g).ker = ⊥ :=
  LinearMap.ker_eq_bot.2 (g.rightInverse_orthogonalRightInverse hg).injective

/-- The range of `orthogonalRightInverse (.id 𝕜 H) g` is `(ker g)ᗮ`. -/
@[simp] theorem range_orthogonalRightInverse (hg : Function.Surjective g) :
    (orthogonalRightInverse (ContinuousLinearMap.id 𝕜 H) g).range = g.kerᗮ := by
  rw [← rightInverseCandidate_eq_orthogonalRightInverse g hg, rightInverseCandidate,
    toLinearMap_comp, ContinuousLinearEquiv.toLinearMap_toContinuousLinearMap,
    LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _),
    Submodule.toLinearMap_subtypeL, Submodule.range_subtype]

omit [CompleteSpace H] [CompleteSpace F] in
/-- **Uniqueness of the Hilbert-space orthogonal right inverse.** Any continuous linear right
inverse of `g` whose range is contained in `(ker g)ᗮ` equals
`orthogonalRightInverse (.id 𝕜 H) g`. -/
theorem eq_orthogonalRightInverse {R : F →L[𝕜] H}
    (hR : g ∘L R = ContinuousLinearMap.id 𝕜 F) (hrange : R.range ≤ g.kerᗮ) :
    R = orthogonalRightInverse (ContinuousLinearMap.id 𝕜 H) g := by
  refine IsOrthogonalRightInverse.eq_orthogonalRightInverse (ι := ContinuousLinearMap.id 𝕜 H)
    Function.injective_id ⟨fun y ↦ DFunLike.congr_fun hR y, fun y k hk ↦ ?_⟩
  dsimp only [ContinuousLinearMap.id_apply]
  exact Submodule.inner_left_of_mem_orthogonal hk (hrange (LinearMap.mem_range_self _ y))

end RightInverse

/-- Every surjective continuous linear map from a Hilbert space onto a Banach space admits a
continuous linear right inverse. -/
theorem HasRightInverse.of_surjective_of_innerProductSpace {g : H →L[𝕜] F}
    (hg : Function.Surjective g) : g.HasRightInverse :=
  ⟨orthogonalRightInverse (ContinuousLinearMap.id 𝕜 H) g,
    g.rightInverse_orthogonalRightInverse hg⟩

end OrthogonalInverses

end ContinuousLinearMap

namespace TauCeti

section ShortExact

open scoped InnerProductSpace

variable {𝕜 E H F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  {f : E →L[𝕜] H} {g : H →L[𝕜] F}

/-- In an algebraically short exact sequence `0 → E --f--> H --g--> F → 0` with `E, F` Banach
spaces and `H` a Hilbert space, the orthogonal left inverse of `f` annihilates the orthogonal
right inverse of `g`. -/
@[simp] theorem orthogonalLeftInverse_comp_orthogonalRightInverse
    (hf : Function.Injective f) (hfg : Function.Exact f g) (hg : Function.Surjective g)
    (hclo : IsClosed (f.range : Set H) := hfg.isClosed_range) :
    f.orthogonalLeftInverse hf hclo ∘L
      ContinuousLinearMap.orthogonalRightInverse (ContinuousLinearMap.id 𝕜 H) g = 0 := by
  apply ContinuousLinearMap.coe_injective
  rw [ContinuousLinearMap.toLinearMap_comp, ContinuousLinearMap.toLinearMap_zero,
    ← LinearMap.range_le_ker_iff, g.range_orthogonalRightInverse hg,
    f.ker_orthogonalLeftInverse hf hclo, (Function.Exact.linearMap_ker_eq hfg).symm]

@[simp] theorem orthogonalLeftInverse_orthogonalRightInverse_apply
    (hf : Function.Injective f) (hfg : Function.Exact f g) (hg : Function.Surjective g)
    (z : F) (hclo : IsClosed (f.range : Set H) := hfg.isClosed_range) :
    f.orthogonalLeftInverse hf hclo
      (ContinuousLinearMap.orthogonalRightInverse (ContinuousLinearMap.id 𝕜 H) g z) = 0 :=
  DFunLike.congr_fun (orthogonalLeftInverse_comp_orthogonalRightInverse hf hfg hg hclo) z

/-- In an algebraically short exact sequence `0 → E --f--> H --g--> F → 0` with `E, F` Banach
spaces and `H` a Hilbert space, the projections `f ∘ ρ` and `σ ∘ g` built from the orthogonal
inverses sum to the identity on `H`. -/
theorem comp_orthogonalLeftInverse_add_orthogonalRightInverse_comp
    (hf : Function.Injective f) (hfg : Function.Exact f g) (hg : Function.Surjective g) :
    f ∘L f.orthogonalLeftInverse hf hfg.isClosed_range +
      ContinuousLinearMap.orthogonalRightInverse (ContinuousLinearMap.id 𝕜 H) g ∘L g =
        ContinuousLinearMap.id 𝕜 H := by
  have : CompleteSpace f.range := hfg.isClosed_range.completeSpace_coe
  have : CompleteSpace g.ker := g.isClosed_ker.completeSpace_coe
  rw [f.self_comp_orthogonalLeftInverse hf hfg.isClosed_range,
    g.orthogonalRightInverse_comp_self hg]
  have hker : f.range = g.ker := (Function.Exact.linearMap_ker_eq hfg).symm
  ext x
  have hproj : f.range.starProjection = g.ker.starProjection := by congr!
  rw [add_apply, hproj, ContinuousLinearMap.id_apply]
  exact Submodule.starProjection_add_starProjection_orthogonal x

private noncomputable def submoduleEquivOfEq {p q : Submodule 𝕜 H} (hpq : p = q) :
    p ≃L[𝕜] q where
  __ := LinearEquiv.ofEq p q hpq
  continuous_toFun := continuous_induced_rng.mpr continuous_subtypeVal
  continuous_invFun := continuous_induced_rng.mpr continuous_subtypeVal

/-- **Orthogonal topological splitting of a short exact sequence through a Hilbert space.**
An algebraically short exact sequence `0 → E --f--> H --g--> F → 0` of bounded linear maps, with
`E, F` Banach spaces and `H` a Hilbert space, induces a canonical continuous linear equivalence
`E × F ≃L[𝕜] H` sending `(x, z)` to `f x + orthogonalRightInverse (.id 𝕜 H) g z`, with
inverse `(f.orthogonalLeftInverse _ _).prod g`. -/
noncomputable def orthogonalShortExactEquiv
    (hf : Function.Injective f) (hfg : Function.Exact f g) (hg : Function.Surjective g) :
    (E × F) ≃L[𝕜] H :=
  have : CompleteSpace f.range := hfg.isClosed_range.completeSpace_coe
  have hclo' : IsClosed (Set.range f) := by
    simpa only [LinearMap.coe_range, ContinuousLinearMap.coe_coe] using hfg.isClosed_range
  let e₁ : E ≃L[𝕜] f.range := f.equivRange hf hclo'
  let e₂ : f.rangeᗮ ≃L[𝕜] F :=
    (submoduleEquivOfEq (p := f.rangeᗮ) (q := g.kerᗮ) (by rw [hfg.linearMap_ker_eq])).trans
      (ContinuousLinearMap.restrictOrthogonalEquiv g hg)
  (e₁.prodCongr e₂.symm).trans
    (f.range.prodEquivOfIsTopCompl f.rangeᗮ f.range.isTopCompl_orthogonal)

@[simp] theorem orthogonalShortExactEquiv_apply
    (hf : Function.Injective f) (hfg : Function.Exact f g) (hg : Function.Surjective g)
    (xz : E × F) :
    orthogonalShortExactEquiv hf hfg hg xz =
      f xz.1 + ContinuousLinearMap.orthogonalRightInverse (ContinuousLinearMap.id 𝕜 H) g xz.2 := by
  have : CompleteSpace f.range := hfg.isClosed_range.completeSpace_coe
  simp only [orthogonalShortExactEquiv, ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.prodCongr_apply, Submodule.prodEquivOfIsTopCompl_apply]
  congr 1
  exact DFunLike.congr_fun (g.rightInverseCandidate_eq_orthogonalRightInverse hg) xz.2

@[simp] theorem orthogonalShortExactEquiv_symm_apply
    (hf : Function.Injective f) (hfg : Function.Exact f g) (hg : Function.Surjective g)
    (y : H) :
    (orthogonalShortExactEquiv hf hfg hg).symm y =
      (f.orthogonalLeftInverse hf hfg.isClosed_range y, g y) := by
  have : CompleteSpace f.range := hfg.isClosed_range.completeSpace_coe
  rw [orthogonalShortExactEquiv, ContinuousLinearEquiv.symm_trans_apply,
    ContinuousLinearEquiv.prodCongr_symm, ContinuousLinearEquiv.prodCongr_apply,
    Submodule.prodEquivOfIsTopCompl_symm_apply]
  ext
  · exact (f.orthogonalLeftInverse_apply hf hfg.isClosed_range y).symm
  · dsimp only [ContinuousLinearEquiv.symm_symm, ContinuousLinearEquiv.trans_apply,
      ContinuousLinearMap.restrictOrthogonalEquiv, ContinuousLinearEquiv.coeFn_ofBijective,
      ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, submoduleEquivOfEq]
    have hsum : (f.range.projectionOntoL f.rangeᗮ f.range.isTopCompl_orthogonal y : H) +
        (f.rangeᗮ.projectionOntoL f.range f.range.isTopCompl_orthogonal.symm y : H) = y :=
      Submodule.projection_add_projection_eq_self f.range.isTopCompl_orthogonal.isCompl y
    have hker :
        g (f.range.projectionOntoL f.rangeᗮ f.range.isTopCompl_orthogonal y : H) = 0 := by
      have hmem : (f.range.projectionOntoL f.rangeᗮ f.range.isTopCompl_orthogonal y : H) ∈
          f.range := Submodule.coe_mem _
      rw [← ContinuousLinearMap.coe_coe, ← LinearMap.mem_ker]
      exact hfg.linearMap_ker_eq.ge hmem
    calc g (f.rangeᗮ.projectionOntoL f.range f.range.isTopCompl_orthogonal.symm y : H)
        = g ((f.range.projectionOntoL f.rangeᗮ f.range.isTopCompl_orthogonal y : H) +
            (f.rangeᗮ.projectionOntoL f.range f.range.isTopCompl_orthogonal.symm y : H)) := by
          rw [map_add, hker, zero_add]
      _ = g y := by rw [hsum]

@[simp] theorem toContinuousLinearMap_orthogonalShortExactEquiv
    (hf : Function.Injective f) (hfg : Function.Exact f g) (hg : Function.Surjective g) :
    (orthogonalShortExactEquiv hf hfg hg : E × F →L[𝕜] H) =
      f.coprod (ContinuousLinearMap.orthogonalRightInverse (ContinuousLinearMap.id 𝕜 H) g) := by
  apply ContinuousLinearMap.ext
  rintro ⟨x, z⟩
  simp

@[simp] theorem toContinuousLinearMap_orthogonalShortExactEquiv_symm
    (hf : Function.Injective f) (hfg : Function.Exact f g) (hg : Function.Surjective g) :
    ((orthogonalShortExactEquiv hf hfg hg).symm : H →L[𝕜] E × F) =
      (f.orthogonalLeftInverse hf hfg.isClosed_range).prod g := by
  ext y <;> simp

end ShortExact

end TauCeti
