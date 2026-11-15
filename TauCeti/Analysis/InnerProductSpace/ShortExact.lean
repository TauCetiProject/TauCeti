/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.ContinuousInverse
public import TauCeti.Analysis.InnerProductSpace.Projection.Basic
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Snake

/-!
# Topological splittings of short exact sequences through Hilbert spaces

When the ambient space is a Hilbert space over an `RCLike` field, the Banach open mapping theorem
combined with orthogonal projection upgrades algebraic injectivity (with closed range) and
algebraic surjectivity to canonical continuous linear one-sided inverses:

* `ContinuousLinearMap.orthogonalLeftInverse`: for an injective bounded map `f : E →L[𝕜] H` from a
  Banach space into a Hilbert space with closed range, the composite
  `(f.equivRange _ _)⁻¹ ∘ P_{im f}` is a continuous linear left inverse of `f` with kernel
  `(range f)ᗮ`.
* `ContinuousLinearMap.orthogonalRightInverse`: for a surjective bounded map `g : H →L[𝕜] F` from a
  Hilbert space onto a Banach space, inverting the bijection `g|_{(ker g)ᗮ} : (ker g)ᗮ → F` gives a
  continuous linear right inverse of `g` with range `(ker g)ᗮ`.

Combined with `Function.Exact.isClosed_range`, every algebraically short exact sequence
`0 → E₁ --f--> H₂ --g--> E₃ → 0` of bounded linear maps with `E₁, E₃` Banach spaces and `H₂` a
Hilbert space splits topologically: `f` admits its orthogonal left inverse `ρ`, `g` admits its
orthogonal right inverse `σ`, and `f.coprod σ` is a continuous linear equivalence
`E₁ × E₃ ≃L[𝕜] H₂` with inverse `ρ.prod g` (`TauCeti.orthogonalShortExactEquiv`).

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

/-- The **orthogonal left inverse** of an injective continuous linear map `f : E →L[𝕜] H` from a
Banach space into a Hilbert space with closed range: project `H` orthogonally onto `range f` and
apply the Banach bounded inverse `(f.equivRange _ _)⁻¹`. -/
noncomputable def orthogonalLeftInverse (f : E →L[𝕜] H) (hf : Function.Injective f)
    (hclo : IsClosed (f.range : Set H)) : H →L[𝕜] E :=
  have : CompleteSpace f.range := hclo.completeSpace_coe
  (f.equivRange hf
    (by simpa only [LinearMap.coe_range, coe_coe] using hclo)).symm.toContinuousLinearMap ∘L
    f.range.orthogonalProjectionOnto

/-- `f.orthogonalLeftInverse` is a left inverse of `f`. -/
theorem leftInverse_orthogonalLeftInverse (f : E →L[𝕜] H) (hf : Function.Injective f)
    (hclo : IsClosed (f.range : Set H)) :
    Function.LeftInverse (f.orthogonalLeftInverse hf hclo) f := fun x ↦ by
  have : CompleteSpace f.range := hclo.completeSpace_coe
  have hclo' : IsClosed (Set.range f) := by simpa only [LinearMap.coe_range, coe_coe] using hclo
  have hproj : (f.range.orthogonalProjectionOnto (f x) : H) = f x := by
    rw [← Submodule.starProjection_apply]
    exact Submodule.starProjection_eq_self_iff.2 (LinearMap.mem_range_self _ x)
  have he : ((f.equivRange hf hclo' x : f.range) : H) = f x :=
    congrArg Subtype.val (DFunLike.congr_fun (f.coe_linearMap_equivRange hf hclo') x)
  simp [orthogonalLeftInverse, ContinuousLinearEquiv.symm_apply_eq, Subtype.ext_iff, hproj, he]

@[simp]
theorem orthogonalLeftInverse_apply_self (f : E →L[𝕜] H) (hf : Function.Injective f)
    (hclo : IsClosed (f.range : Set H)) (x : E) :
    f.orthogonalLeftInverse hf hclo (f x) = x :=
  f.leftInverse_orthogonalLeftInverse hf hclo x

@[simp]
theorem orthogonalLeftInverse_comp_self (f : E →L[𝕜] H) (hf : Function.Injective f)
    (hclo : IsClosed (f.range : Set H)) :
    f.orthogonalLeftInverse hf hclo ∘L f = ContinuousLinearMap.id 𝕜 E :=
  ContinuousLinearMap.ext (f.leftInverse_orthogonalLeftInverse hf hclo)

/-- Composing `f` on the left of its orthogonal left inverse recovers the orthogonal projection
onto `range f`. -/
@[simp]
theorem self_comp_orthogonalLeftInverse (f : E →L[𝕜] H) [f.range.HasOrthogonalProjection]
    (hf : Function.Injective f) (hclo : IsClosed (f.range : Set H)) :
    f ∘L f.orthogonalLeftInverse hf hclo = f.range.starProjection := by
  have : CompleteSpace f.range := hclo.completeSpace_coe
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
@[simp]
theorem ker_orthogonalLeftInverse (f : E →L[𝕜] H) (hf : Function.Injective f)
    (hclo : IsClosed (f.range : Set H)) :
    (f.orthogonalLeftInverse hf hclo).ker = f.rangeᗮ := by
  have : CompleteSpace f.range := hclo.completeSpace_coe
  rw [orthogonalLeftInverse, toLinearMap_comp,
    ContinuousLinearEquiv.toLinearMap_toContinuousLinearMap, LinearEquiv.ker_comp]
  exact Submodule.ker_orthogonalProjectionOnto

/-- `f.orthogonalLeftInverse` is surjective, so its range is `⊤`. -/
@[simp]
theorem range_orthogonalLeftInverse (f : E →L[𝕜] H) (hf : Function.Injective f)
    (hclo : IsClosed (f.range : Set H)) :
    (f.orthogonalLeftInverse hf hclo).range = ⊤ :=
  LinearMap.range_eq_top.2 (f.leftInverse_orthogonalLeftInverse hf hclo).surjective

/-- An injective continuous linear map from a Banach space into a Hilbert space with closed range
has a continuous linear left inverse. Unlike
`ContinuousLinearMap.HasLeftInverse.of_injective_of_isClosed_range_of_closedComplement_range`, no
closed-complement hypothesis is needed because `H` is a Hilbert space. -/
theorem HasLeftInverse.of_injective_of_isClosed_range {f : E →L[𝕜] H}
    (hf : Function.Injective f) (hclo : IsClosed (f.range : Set H)) :
    f.HasLeftInverse :=
  ⟨f.orthogonalLeftInverse hf hclo, f.leftInverse_orthogonalLeftInverse hf hclo⟩

/-- In an exact sequence `0 → E --f--> H` followed by `H --q--> G`, with `E` a Banach space, `H` a
Hilbert space, and `G` a `T₁` topological module, `f` admits a continuous linear left inverse. -/
theorem HasLeftInverse.of_injective_of_exact {G : Type*} [TopologicalSpace G] [AddCommMonoid G]
    [Module 𝕜 G] [T1Space G] {f : E →L[𝕜] H} {q : H →L[𝕜] G}
    (hf : Function.Injective f) (hfq : Function.Exact f q) :
    f.HasLeftInverse :=
  .of_injective_of_isClosed_range hf hfq.isClosed_range

/-- The **orthogonal right inverse** of a surjective continuous linear map `g : H →L[𝕜] F` from a
Hilbert space onto a Banach space: invert the bounded bijection `g|_{(ker g)ᗮ} : (ker g)ᗮ → F` via
`ContinuousLinearEquiv.ofBijective` and include `(ker g)ᗮ` into `H`. -/
noncomputable def orthogonalRightInverse (g : H →L[𝕜] F) (hg : Function.Surjective g) :
    F →L[𝕜] H :=
  have : CompleteSpace g.ker := g.isClosed_ker.completeSpace_coe
  g.kerᗮ.subtypeL ∘L
    (ContinuousLinearEquiv.ofBijective (g ∘L g.kerᗮ.subtypeL) g.ker_comp_subtypeL_orthogonal
      (g.range_comp_subtypeL_orthogonal.trans
        (LinearMap.range_eq_top.2 hg))).symm.toContinuousLinearMap

/-- `g.orthogonalRightInverse` is a right inverse of `g`. -/
theorem rightInverse_orthogonalRightInverse (g : H →L[𝕜] F) (hg : Function.Surjective g) :
    Function.RightInverse (g.orthogonalRightInverse hg) g := fun y ↦ by
  rw [orthogonalRightInverse, comp_apply, ContinuousLinearEquiv.coe_coe,
    ← comp_apply g g.kerᗮ.subtypeL, ContinuousLinearEquiv.ofBijective_apply_symm_apply]

@[simp]
theorem apply_orthogonalRightInverse (g : H →L[𝕜] F) (hg : Function.Surjective g) (y : F) :
    g (g.orthogonalRightInverse hg y) = y :=
  g.rightInverse_orthogonalRightInverse hg y

@[simp]
theorem self_comp_orthogonalRightInverse (g : H →L[𝕜] F) (hg : Function.Surjective g) :
    g ∘L g.orthogonalRightInverse hg = ContinuousLinearMap.id 𝕜 F :=
  ContinuousLinearMap.ext (g.rightInverse_orthogonalRightInverse hg)

/-- Composing `g.orthogonalRightInverse` on the left of `g` recovers the orthogonal projection onto
`(ker g)ᗮ`. -/
@[simp]
theorem orthogonalRightInverse_comp_self (g : H →L[𝕜] F) (hg : Function.Surjective g) :
    g.orthogonalRightInverse hg ∘L g = g.kerᗮ.starProjection := by
  have : CompleteSpace g.ker := g.isClosed_ker.completeSpace_coe
  set e := ContinuousLinearEquiv.ofBijective (g ∘L g.kerᗮ.subtypeL)
    g.ker_comp_subtypeL_orthogonal
    (g.range_comp_subtypeL_orthogonal.trans (LinearMap.range_eq_top.2 hg))
  ext x
  have hx : e (g.kerᗮ.orthogonalProjectionOnto x) = g x := by
    simp only [e, ContinuousLinearEquiv.coeFn_ofBijective, comp_apply, Submodule.subtypeL_apply,
      Submodule.coe_orthogonalProjectionOnto_apply]
    exact DFunLike.congr_fun g.comp_starProjection_orthogonal_ker x
  have hsymm : e.symm (g x) = g.kerᗮ.orthogonalProjectionOnto x :=
    e.injective (by rw [e.apply_symm_apply, hx])
  simpa only [orthogonalRightInverse, comp_apply, Submodule.subtypeL_apply,
    ContinuousLinearEquiv.coe_coe, Submodule.starProjection_apply] using
    congrArg Subtype.val hsymm

/-- `g.orthogonalRightInverse` is injective, so its kernel is `⊥`. -/
@[simp]
theorem ker_orthogonalRightInverse (g : H →L[𝕜] F) (hg : Function.Surjective g) :
    (g.orthogonalRightInverse hg).ker = ⊥ :=
  LinearMap.ker_eq_bot.2 (g.rightInverse_orthogonalRightInverse hg).injective

/-- The range of `g.orthogonalRightInverse` is `(ker g)ᗮ`. -/
@[simp]
theorem range_orthogonalRightInverse (g : H →L[𝕜] F) (hg : Function.Surjective g) :
    (g.orthogonalRightInverse hg).range = g.kerᗮ := by
  rw [orthogonalRightInverse, toLinearMap_comp,
    ContinuousLinearEquiv.toLinearMap_toContinuousLinearMap,
    LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _),
    Submodule.toLinearMap_subtypeL, Submodule.range_subtype]

/-- Every surjective continuous linear map from a Hilbert space onto a Banach space admits a
continuous linear right inverse. -/
theorem HasRightInverse.of_surjective {g : H →L[𝕜] F} (hg : Function.Surjective g) :
    g.HasRightInverse :=
  ⟨g.orthogonalRightInverse hg, g.rightInverse_orthogonalRightInverse hg⟩

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
@[simp]
theorem orthogonalLeftInverse_comp_orthogonalRightInverse
    (hf : Function.Injective f) (hfg : Function.Exact f g) (hg : Function.Surjective g)
    (hclo : IsClosed (f.range : Set H) := hfg.isClosed_range) :
    f.orthogonalLeftInverse hf hclo ∘L g.orthogonalRightInverse hg = 0 := by
  -- Show the range `(ker g)ᗮ` lies in the kernel `(range f)ᗮ`.
  apply ContinuousLinearMap.coe_injective
  rw [ContinuousLinearMap.toLinearMap_comp, ContinuousLinearMap.toLinearMap_zero,
    ← LinearMap.range_le_ker_iff, g.range_orthogonalRightInverse hg,
    f.ker_orthogonalLeftInverse hf hclo,
    (Function.Exact.linearMap_ker_eq hfg).symm]

@[simp]
theorem orthogonalLeftInverse_orthogonalRightInverse_apply
    (hf : Function.Injective f) (hfg : Function.Exact f g) (hg : Function.Surjective g)
    (z : F) (hclo : IsClosed (f.range : Set H) := hfg.isClosed_range) :
    f.orthogonalLeftInverse hf hclo (g.orthogonalRightInverse hg z) = 0 :=
  DFunLike.congr_fun (orthogonalLeftInverse_comp_orthogonalRightInverse hf hfg hg hclo) z

/-- In an algebraically short exact sequence `0 → E --f--> H --g--> F → 0` with `E, F` Banach
spaces and `H` a Hilbert space, the projections `f ∘ ρ` and `σ ∘ g` built from the orthogonal
inverses sum to the identity on `H`. -/
theorem comp_orthogonalLeftInverse_add_orthogonalRightInverse_comp
    (hf : Function.Injective f) (hfg : Function.Exact f g) (hg : Function.Surjective g) :
    f ∘L f.orthogonalLeftInverse hf hfg.isClosed_range +
      g.orthogonalRightInverse hg ∘L g = ContinuousLinearMap.id 𝕜 H := by
  have : CompleteSpace f.range := hfg.isClosed_range.completeSpace_coe
  have : CompleteSpace g.ker := g.isClosed_ker.completeSpace_coe
  rw [f.self_comp_orthogonalLeftInverse hf hfg.isClosed_range,
    g.orthogonalRightInverse_comp_self hg]
  have hker : f.range = g.ker := (Function.Exact.linearMap_ker_eq hfg).symm
  ext x
  have hproj : f.range.starProjection = g.ker.starProjection := by congr!
  rw [add_apply, hproj, ContinuousLinearMap.id_apply]
  exact Submodule.starProjection_add_starProjection_orthogonal x

/-- **Orthogonal topological splitting of a short exact sequence through a Hilbert space.**
An algebraically short exact sequence `0 → E --f--> H --g--> F → 0` of bounded linear maps, with
`E, F` Banach spaces and `H` a Hilbert space, induces a canonical continuous linear equivalence
`E × F ≃L[𝕜] H` sending `(x, z)` to `f x + g.orthogonalRightInverse hg z`, with inverse
`(f.orthogonalLeftInverse _ _).prod g`. -/
noncomputable def orthogonalShortExactEquiv
    (hf : Function.Injective f) (hfg : Function.Exact f g) (hg : Function.Surjective g) :
    (E × F) ≃L[𝕜] H :=
  let ρ := f.orthogonalLeftInverse hf hfg.isClosed_range
  let σ := g.orthogonalRightInverse hg
  ContinuousLinearEquiv.equivOfInverse (f.coprod σ) (ρ.prod g)
    (fun ⟨x, z⟩ ↦ Prod.ext
      (by simp [ρ, σ, hfg])
      (by simp [σ, hfg.apply_apply_eq_zero x]))
    (fun y ↦ by
      simpa only [ContinuousLinearMap.coprod_apply, ContinuousLinearMap.prod_apply,
        ← ContinuousLinearMap.comp_apply, ← add_apply,
        ContinuousLinearMap.id_apply] using
        DFunLike.congr_fun (comp_orthogonalLeftInverse_add_orthogonalRightInverse_comp hf hfg hg) y)

@[simp]
theorem orthogonalShortExactEquiv_apply
    (hf : Function.Injective f) (hfg : Function.Exact f g) (hg : Function.Surjective g)
    (xz : E × F) :
    orthogonalShortExactEquiv hf hfg hg xz = f xz.1 + g.orthogonalRightInverse hg xz.2 :=
  (rfl)

@[simp]
theorem orthogonalShortExactEquiv_symm_apply
    (hf : Function.Injective f) (hfg : Function.Exact f g) (hg : Function.Surjective g) (y : H) :
    (orthogonalShortExactEquiv hf hfg hg).symm y =
      (f.orthogonalLeftInverse hf hfg.isClosed_range y, g y) :=
  (rfl)

@[simp]
theorem toContinuousLinearMap_orthogonalShortExactEquiv
    (hf : Function.Injective f) (hfg : Function.Exact f g) (hg : Function.Surjective g) :
    (orthogonalShortExactEquiv hf hfg hg : E × F →L[𝕜] H) =
      f.coprod (g.orthogonalRightInverse hg) :=
  (rfl)

@[simp]
theorem toContinuousLinearMap_orthogonalShortExactEquiv_symm
    (hf : Function.Injective f) (hfg : Function.Exact f g) (hg : Function.Surjective g) :
    ((orthogonalShortExactEquiv hf hfg hg).symm : H →L[𝕜] E × F) =
      (f.orthogonalLeftInverse hf hfg.isClosed_range).prod g :=
  (rfl)

end ShortExact

end TauCeti
