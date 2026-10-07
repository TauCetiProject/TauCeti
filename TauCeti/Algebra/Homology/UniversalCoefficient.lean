/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Ext.Presentation
public import TauCeti.Algebra.Homology.Kronecker
public import TauCeti.Algebra.Homology.ShortComplex.ShortExact

/-!
# The universal coefficient sequence for cohomology

Let `X` be a chain complex in a `k`-linear abelian category `C`, with `k` commutative, and let
`Y : C`. In degree `i = j + 1`, write `Zⱼ` for the cycles of `X`, `Bⱼ = ker(Zⱼ ⟶ Hⱼ(X))` for the
boundaries, and `Hⁱ(Hom(X, Y))` for the cohomology of the cochain complex
`ChainComplex.linearYonedaObj`. This file proves that

`0 ⟶ Ext¹(Hⱼ(X), Y) ⟶ Hⁱ(Hom(X, Y)) ⟶ (Hᵢ(X) ⟶ Y) ⟶ 0`

is exact and split when the inclusions of the cycles `Zᵢ ⟶ Xᵢ` and `Zⱼ ⟶ Xⱼ` are split
monomorphisms and `Zⱼ` is projective. The second map is the Kronecker map
`TauCeti.ChainComplex.kronecker`, which `TauCeti.ChainComplex.kroneckerSection` splits (in
`TauCeti.Algebra.Homology.Kronecker`). This is the universal coefficient theorem for cohomology.
Over a hereditary ring, such as a principal ideal domain, these hypotheses hold for a degreewise
projective complex: the cycles and the boundaries are submodules of projective modules, hence
projective, and a surjection onto the projective boundaries splits.

The first map is built from the extension class of `0 ⟶ Bⱼ ⟶ Zⱼ ⟶ Hⱼ(X) ⟶ 0`. A morphism
`β : Bⱼ ⟶ Y` gives the cocycle `Xᵢ ⟶ Bⱼ ⟶ Y` of `Hom(X, Y)`, through the corestriction of the
differential `Xᵢ ⟶ Xⱼ` to the boundaries. Its class depends only on the image of `β` in
`Ext¹(Hⱼ(X), Y)`, and every element of `Ext¹(Hⱼ(X), Y)` is such an image: the map factors through
the identification `TauCeti.homCokernelEquivExt` of `Ext¹(Hⱼ(X), Y)` with `Hom(Bⱼ, Y)` modulo the
morphisms extending to `Zⱼ`.

## Main declarations

* `TauCeti.ChainComplex.extToHomology`: the map `Ext¹(Hⱼ(X), Y) →ₗ[k] Hⁱ(Hom(X, Y))`,
  characterized by `TauCeti.ChainComplex.extToHomology_extClass_comp_mk₀`.
* `TauCeti.ChainComplex.extToHomology_injective` and
  `TauCeti.ChainComplex.exact_extToHomology_kronecker`: exactness at the first two places.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.1, Theorem 3.2.
* C. A. Weibel, *An Introduction to Homological Algebra*, Cambridge Studies in Advanced
  Mathematics 38, Cambridge University Press (1994), Theorem 3.6.5.
-/

public section

noncomputable section

open CategoryTheory Limits HomologicalComplex Abelian

universe w

namespace TauCeti.ChainComplex

variable {C : Type*} [Category* C] [Abelian C] {α : Type*} [AddRightCancelSemigroup α] [One α]

section Ext

variable {k : Type*} [CommRing k] [Linear k C] [HasExt.{w} C] {X : ChainComplex C α} {Y : C}

/-- The corestriction `Xᵢ ⟶ Bⱼ` of the differential to the boundaries `ker(Zⱼ ⟶ Hⱼ(X))`. -/
private abbrev toBoundaries (i j : α) : X.X i ⟶ kernel (X.homologyπ j) :=
  kernel.lift _ (X.toCycles i j) (X.toCycles_comp_homologyπ i j)

omit [HasExt C] in
/-- The corestriction of the differential to the boundaries vanishes on boundaries. -/
private lemma d_toBoundaries (i j : α) :
    X.d ((ComplexShape.up α).next i) i ≫ toBoundaries (X := X) i j = 0 := by
  rw [← cancel_mono (kernel.ι _), Category.assoc, kernel.lift_ι, X.d_toCycles, zero_comp]

omit [HasExt C] in
/-- In degree `i = j + 1`, the corestriction of the differential to the boundaries is an
epimorphism, because the homology `Hⱼ(X)` is the cokernel of `Xᵢ ⟶ Zⱼ`. -/
private lemma epi_toBoundaries {i j : α} (hij : j + 1 = i) : Epi (toBoundaries (X := X) i j) :=
  (ShortComplex.exact_of_g_is_cokernel
    (ShortComplex.mk (X.toCycles i j) (X.homologyπ j) (X.toCycles_comp_homologyπ i j))
    (X.homologyIsCokernel i j ((ComplexShape.down α).prev_eq' hij))).epi_kernelLift

variable (k Y) in
/-- The map `Hom(Bⱼ, Y) →ₗ[k] Hⁱ(Hom(X, Y))` sending `β` to the class of the cocycle
`Xᵢ ⟶ Bⱼ ⟶ Y`. -/
private abbrev boundariesHom (i j : α) :
    (kernel (X.homologyπ j) ⟶ Y) →ₗ[k] (X.linearYonedaObj k Y).homology i :=
  homologyClassOfComp k Y (toBoundaries (X := X) i j) (d_toBoundaries i j)

omit [HasExt C] in
/-- `TauCeti.kernelSequence_shortExact` for `0 ⟶ Bⱼ ⟶ Zⱼ ⟶ Hⱼ(X) ⟶ 0`, with the terms of the
sequence unfolded, so that its extension class has source `Hⱼ(X)` and target `Bⱼ` up to
reducible defeq. -/
private lemma boundaries_shortExact (j : α) :
    (ShortComplex.mk (kernel.ι (X.homologyπ j)) (X.homologyπ j) (kernel.condition _)).ShortExact :=
  kernelSequence_shortExact (X.homologyπ j)

omit [HasExt C] in
/-- A morphism `Bⱼ ⟶ Y` extending to the cycles `Zⱼ` gives a coboundary, when the inclusion of
the cycles `Zⱼ ⟶ Xⱼ` is split: it extends to `Xⱼ`. -/
private lemma range_leftComp_le_ker (i j : α) [IsSplitMono (X.iCycles j)] :
    LinearMap.range (Linear.leftComp k Y (kernel.ι (X.homologyπ j))) ≤
      LinearMap.ker (boundariesHom k Y (X := X) i j) := by
  rintro _ ⟨γ, rfl⟩
  -- `Xᵢ ⟶ Bⱼ ⟶ Zⱼ ⟶ Y` is the coboundary of `Xⱼ ⟶ Zⱼ ⟶ Y`, using the retraction of `Zⱼ ⟶ Xⱼ`
  rw [LinearMap.mem_ker, homologyClassOfComp_eq _ _ _
    ((X.linearYonedaObj k Y).toCycles j i (retraction (X.iCycles j) ≫ γ))
    ((linearYonedaObj_iCycles_toCycles_apply j i _).trans (by
      rw [Linear.leftComp_apply, kernel.lift_ι_assoc, ← X.toCycles_i_assoc,
        IsSplitMono.id_assoc]))]
  exact linearYonedaObj_homologyπ_toCycles_apply j i _

variable (k X Y) in
/-- **The `Ext` term of the universal coefficient sequence**: the `k`-linear map
`Ext¹(Hⱼ(X), Y) →ₗ[k] Hⁱ(Hom(X, Y))`. The image of `β : Bⱼ ⟶ Y` under precomposition with the
extension class of `0 ⟶ Bⱼ ⟶ Zⱼ ⟶ Hⱼ(X) ⟶ 0` goes to the class of the cocycle `Xᵢ ⟶ Bⱼ ⟶ Y`
(`TauCeti.ChainComplex.extToHomology_extClass_comp_mk₀`). It is defined when the cycles `Zⱼ` are
projective and their inclusion `Zⱼ ⟶ Xⱼ` is split, and is injective when `i = j + 1`. -/
def extToHomology (i j : α) [Projective (X.cycles j)] [IsSplitMono (X.iCycles j)] :
    Ext.{w} (X.homology j) Y 1 →ₗ[k] (X.linearYonedaObj k Y).homology i :=
  ((LinearMap.range _).liftQ (boundariesHom k Y (X := X) i j) (range_leftComp_le_ker i j)).comp
    (homCokernelEquivExt k (boundaries_shortExact j) Y).symm.toLinearMap

/-- `TauCeti.ChainComplex.extToHomology` sends the image of `β : Bⱼ ⟶ Y` in `Ext¹(Hⱼ(X), Y)` to
the class of the cocycle `Xᵢ ⟶ Bⱼ ⟶ Y`. -/
private lemma extToHomology_homBoundary (i j : α) [Projective (X.cycles j)]
    [IsSplitMono (X.iCycles j)] (β : kernel (X.homologyπ j) ⟶ Y) :
    extToHomology.{w} k X Y i j (homBoundary k (boundaries_shortExact j) Y β) =
      boundariesHom k Y i j β := by
  rw [homBoundary_apply, extToHomology, LinearMap.comp_apply, LinearEquiv.coe_coe,
    homCokernelEquivExt_symm_comp_mk₀, Submodule.liftQ_apply]

/-- **The characterization of `TauCeti.ChainComplex.extToHomology`**: the class in `Ext¹(Hⱼ(X), Y)`
of a morphism `β : Bⱼ ⟶ Y` from the boundaries goes to the class of the cocycle `Xᵢ ⟶ Bⱼ ⟶ Y`. -/
lemma extToHomology_extClass_comp_mk₀ (i j : α) [Projective (X.cycles j)]
    [IsSplitMono (X.iCycles j)] (β : kernel (X.homologyπ j) ⟶ Y)
    (φ : (X.linearYonedaObj k Y).cycles i)
    (hφ : (X.linearYonedaObj k Y).iCycles i φ =
      kernel.lift _ (X.toCycles i j) (X.toCycles_comp_homologyπ i j) ≫ β) :
    extToHomology k X Y i j
        ((kernelSequence_shortExact (X.homologyπ j)).extClass.comp (Ext.mk₀ β) (add_zero 1)) =
      (X.linearYonedaObj k Y).homologyπ i φ := by
  -- the extension classes of `kernelSequence` and of its unfolding agree by definition
  have h := congrArg (extToHomology k X Y i j) (homBoundary_apply k (boundaries_shortExact j) Y β)
  exact h.symm.trans ((extToHomology_homBoundary i j β).trans (homologyClassOfComp_eq _ _ β φ hφ))

/-- **Injectivity in the universal coefficient sequence**: in degree `i = j + 1`, the map
`Ext¹(Hⱼ(X), Y) →ₗ[k] Hⁱ(Hom(X, Y))` is injective. If the cocycle `Xᵢ ⟶ Bⱼ ⟶ Y` is the coboundary
of `ψ : Xⱼ ⟶ Y`, then `β` is the restriction of `ψ` to `Bⱼ`, so it extends to `Zⱼ` and its
class in `Ext¹(Hⱼ(X), Y)` vanishes. -/
theorem extToHomology_injective {i j : α} (hij : j + 1 = i) [Projective (X.cycles j)]
    [IsSplitMono (X.iCycles j)] : Function.Injective (extToHomology.{w} k X Y i j) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro e he
  obtain ⟨β, rfl⟩ := homBoundary_surjective k (boundaries_shortExact (X := X) j) Y e
  have hβ : boundariesHom k Y i j β = 0 := (extToHomology_homBoundary i j β).symm.trans he
  -- the cocycle `Xᵢ ⟶ Bⱼ ⟶ Y` is a coboundary `Xᵢ ⟶ Xⱼ ⟶ Y`
  have hφ := iCycles_cocycleOfComp (k := k) _ (d_toBoundaries i j) β
  rw [homologyClassOfComp_eq _ _ β _ hφ] at hβ
  obtain ⟨ψ, hψ⟩ := ((ShortComplex.moduleCat_exact_iff _).1
    (ShortComplex.exact_of_g_is_cokernel (ShortComplex.mk _ _
      ((X.linearYonedaObj k Y).toCycles_comp_homologyπ j i))
      ((X.linearYonedaObj k Y).homologyIsCokernel j i ((ComplexShape.up α).prev_eq' hij)))) _ hβ
  rw [← hψ, linearYonedaObj_iCycles_toCycles_apply] at hφ
  -- name the cochain `ψ` with its morphism type `Xⱼ ⟶ Y`, so that composites with it rewrite
  obtain ⟨ψ', rfl⟩ : ∃ ψ' : X.X j ⟶ Y, ψ' = ψ := ⟨ψ, rfl⟩
  have := epi_toBoundaries (X := X) hij
  -- hence `β` is the restriction of `ψ` along `Bⱼ ⟶ Zⱼ ⟶ Xⱼ`, whose class in `Ext¹` vanishes
  have hβψ : kernel.ι (X.homologyπ j) ≫ X.iCycles j ≫ ψ' = β := by
    rw [← cancel_epi (toBoundaries (X := X) i j), ← hφ, kernel.lift_ι_assoc, X.toCycles_i_assoc]
  exact LinearMap.mem_ker.1
    ((ker_homBoundary k (boundaries_shortExact j) Y).ge ⟨X.iCycles j ≫ ψ', hβψ⟩)

/-- **Exactness in the middle of the universal coefficient sequence**: in degree `i = j + 1`, a
cohomology class of `Hom(X, Y)` evaluates to zero on homology exactly when it comes from
`Ext¹(Hⱼ(X), Y)`. A cocycle vanishing on the cycles `Zᵢ` factors through the corestriction
`Xᵢ ⟶ Bⱼ` of the differential, which is the cokernel of `Zᵢ ⟶ Xᵢ`. -/
theorem exact_extToHomology_kronecker {i j : α} (hij : j + 1 = i) [Projective (X.cycles j)]
    [IsSplitMono (X.iCycles j)] :
    Function.Exact (extToHomology.{w} k X Y i j) (kronecker k X Y i) := by
  have hrange : LinearMap.range (extToHomology.{w} k X Y i j) =
      LinearMap.range (boundariesHom k Y (X := X) i j) := by
    rw [extToHomology, LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _),
      Submodule.range_liftQ]
  rw [LinearMap.exact_iff, hrange]
  refine le_antisymm (fun x hx ↦ ?_) ?_
  · obtain ⟨φ, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ i x
    obtain ⟨a, ha⟩ : ∃ a : X.X i ⟶ Y, (X.linearYonedaObj k Y).iCycles i φ = a := ⟨_, rfl⟩
    have hcyc : X.iCycles i ≫ a = 0 := by
      rw [← ha, ← kronecker_homologyπ, LinearMap.mem_ker.1 hx, comp_zero]
    have := epi_toBoundaries (X := X) hij
    -- the kernel of `Xᵢ ⟶ Bⱼ` lies in the cycles `Zᵢ`, on which the cocycle vanishes
    have hker : kernel.ι (toBoundaries (X := X) i j) ≫ a = 0 := by
      have hd : kernel.ι (toBoundaries (X := X) i j) ≫ X.d i j = 0 := by
        rw [← X.toCycles_i, ← kernel.lift_ι _ _ (X.toCycles_comp_homologyπ i j), Category.assoc,
          kernel.condition_assoc, zero_comp]
      rw [← X.liftCycles_i _ j ((ComplexShape.down α).next_eq' hij) hd, Category.assoc, hcyc,
        comp_zero]
    obtain ⟨β, hβ⟩ := CokernelCofork.IsColimit.desc' (Abelian.epiIsCokernelOfKernel _
      (kernelIsKernel (toBoundaries (X := X) i j))) a hker
    exact ⟨β, homologyClassOfComp_eq _ _ β φ (ha.trans hβ.symm)⟩
  · rintro _ ⟨β, rfl⟩
    -- the cycles `Zᵢ` map to zero in `Bⱼ ⊆ Zⱼ ⊆ Xⱼ`, as `Zᵢ ⟶ Xᵢ ⟶ Xⱼ` vanishes
    have h0 : X.iCycles i ≫ toBoundaries (X := X) i j = 0 := by
      rw [← cancel_mono (kernel.ι (X.homologyπ j)), ← cancel_mono (X.iCycles j)]
      simp only [Category.assoc, kernel.lift_ι, X.toCycles_i, X.iCycles_d, zero_comp]
    rw [LinearMap.mem_ker, ← cancel_epi (X.homologyπ i), homologyπ_kronecker_homologyClassOfComp,
      reassoc_of% h0, zero_comp, comp_zero]

end Ext

end TauCeti.ChainComplex
