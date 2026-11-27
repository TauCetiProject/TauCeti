/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import TauCeti.Algebra.Homology.HomologicalComplex.Basic
public import TauCeti.Algebra.Homology.ShortComplex.ShortExact
public import TauCeti.AlgebraicGeometry.Cohomology.Affine
public import TauCeti.AlgebraicGeometry.Cohomology.LongExactSequence
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.WeakSerre
import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Images
public import TauCeti.AlgebraicGeometry.Modules.Restriction.Basic
public import TauCeti.AlgebraicGeometry.Modules.Tensor.Product
public import TauCeti.Topology.Sheaves.Exact

/-!
# Global sections and the cohomology sheaves of a complex

Let `X` be a scheme. Global sections `Γ(X, -)` are left exact, so for a complex `K` of
`𝒪_X`-modules they always commute with cycles, but in general not with cohomology: the
cohomology `Hᵐ(Γ(X, K))` of the complex of global sections and the global sections `Γ(X, Hᵐ(K))`
of the cohomology sheaf differ. This file gives conditions under which they agree, in the strong
form that `Γ(X, -)` preserves the homology of the short complex `K.sc m`, so that Mathlib's
`ShortComplex.mapHomologyIso` identifies `Hᵐ(Γ(X, K))` with `Γ(X, Hᵐ(K))` naturally.

* `Scheme.Modules.shortExact_map_sectionsFunctor`: global sections of a short exact sequence of
  `𝒪_X`-modules whose last map is surjective on global sections are short exact.
* `Scheme.Modules.exactAt_of_forall_isAffineOpen`: exactness of a complex of `𝒪_X`-modules follows
  from exactness of the global sections of its restrictions to all affine opens.
* `Scheme.Modules.preservesLeftHomologyOf_sectionsFunctor`: for a short complex
  `S = (M₁ ⟶ M₂ ⟶ M₃)`, global sections preserve the homology of `S` as soon as the kernel and
  the image of `M₁ ⟶ ker(M₂ ⟶ M₃)` have vanishing first cohomology.
* `Scheme.Modules.preservesLeftHomologyOf_sectionsFunctor_of_isQuasicoherent`: on an affine
  scheme, global sections preserve the homology of a short complex of quasi-coherent modules, by
  Serre's vanishing theorem.
* `Scheme.Modules.preservesLeftHomologyOf_sectionsFunctor_sc`: if `K` is bounded below, and its
  terms and its cohomology sheaves have no higher cohomology, then the sheaves of cycles and
  boundaries of `K` have no higher cohomology
  (`Scheme.Modules.subsingleton_cohomology_cycles_and_image_toCycles`), and global sections
  preserve the homology of every `K.sc m`. On an affine scheme this applies to a bounded below
  complex of injective modules whose cohomology sheaves are quasi-coherent.

The proof of the second statement is the usual dimension shifting along the short exact
sequences `0 ⟶ Zⁱ ⟶ Kⁱ ⟶ Bⁱ⁺¹ ⟶ 0` and `0 ⟶ Bⁱ ⟶ Zⁱ ⟶ Hⁱ ⟶ 0`, by induction on `i` starting
below the lowest nonzero term.

These statements are the bounded below input to the computation of the cohomology of unbounded
complexes with quasi-coherent cohomology on affine schemes, in
`TauCeti.AlgebraicGeometry.Modules.Derived.Affine.Sections`.

## References

* [Stacks: Section 36.3](https://stacks.math.columbia.edu/tag/06YZ), complexes with
  quasi-coherent cohomology on affine schemes.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- Global sections of a short exact sequence of `𝒪_X`-modules whose last map is surjective on
global sections form a short exact sequence of modules. -/
theorem shortExact_map_sectionsFunctor {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (hg : Function.Surjective (S.g.app ⊤)) :
    (S.map (Scheme.Modules.sectionsFunctor (⊤ : X.Opens))).ShortExact :=
  have := hS.mono_f
  ModuleCat.shortComplex_shortExact _ (exact_sections hS) (sections_injective S.f) hg

/-- **Global sections preserve the homology of a short complex with acyclic boundaries.** For a
short complex `S = (M₁ ⟶ M₂ ⟶ M₃)` of `𝒪_X`-modules, if the kernel and the image of the map
`M₁ ⟶ ker(M₂ ⟶ M₃)` have vanishing first cohomology, then global sections preserve the
homology of `S`: the homology of the complex of global sections is the module of global sections
of the homology. -/
theorem preservesLeftHomologyOf_sectionsFunctor (S : ShortComplex X.Modules)
    (h₁ : Subsingleton (Cohomology (kernel S.toCycles) 1))
    (h₂ : Subsingleton (Cohomology (image S.toCycles) 1)) :
    (Scheme.Modules.sectionsFunctor (⊤ : X.Opens)).PreservesLeftHomologyOf S := by
  let G := Scheme.Modules.sectionsFunctor (⊤ : X.Opens)
  -- global sections preserve the cokernel of `S.toCycles`: on global sections,
  -- `Γ(M₁) ⟶ Γ(ker) ⟶ Γ(coker) ⟶ 0` is exact
  have hK := (ShortComplex.exact_kernel S.toCycles).shortExact_factorThruImage
  have hI := ShortComplex.shortExact_image_ι_cokernel_π S.toCycles
  have hsurj : Function.Surjective ((cokernel.π S.toCycles).app ⊤) := sections_surjective hI h₂
  have : Epi (G.map (factorThruImage S.toCycles)) :=
    (ModuleCat.epi_iff_surjective _).2 (sections_surjective hK h₁)
  have hI' := shortExact_map_sectionsFunctor hI hsurj
  have := hI'.epi_g
  have hcok : IsColimit ((CokernelCofork.ofπ (cokernel.π S.toCycles)
      (cokernel.condition S.toCycles)).map G) :=
    isCokernelEpiComp hI'.exact.gIsCokernel
      (G.map (factorThruImage S.toCycles)) (by
        -- Expose the mapped short complex's first map so G.map_comp applies.
        change G.map S.toCycles = G.map _ ≫ G.map _
        rw [← G.map_comp, image.fac])
  have : PreservesColimit (parallelPair S.toCycles 0) G :=
    preservesColimit_of_preserves_colimit_cocone (cokernelIsCokernel S.toCycles)
      ((CokernelCofork.isColimitMapCoconeEquiv _ _).symm hcok)
  have : S.leftHomologyData.IsPreservedBy G := { g := inferInstance, f' := this }
  exact Functor.PreservesLeftHomologyOf.mk' G S.leftHomologyData

/-- **Global sections preserve the homology of quasi-coherent short complexes on affine schemes.**
On an affine scheme, global sections preserve the homology of a short complex whose first two
terms are quasi-coherent: the kernel and image of its first map are quasi-coherent and acyclic. -/
theorem preservesLeftHomologyOf_sectionsFunctor_of_isQuasicoherent [IsAffine X]
    (S : ShortComplex X.Modules) [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] :
    (Scheme.Modules.sectionsFunctor (⊤ : X.Opens)).PreservesLeftHomologyOf S := by
  let eK : kernel S.toCycles ≅ kernel S.f :=
    (kernelCompMono S.toCycles S.iCycles).symm ≪≫ kernelIsoOfEq S.toCycles_i
  let eI : image S.toCycles ≅ image S.f :=
    image.isoStrongEpiMono (factorThruImage S.toCycles) (image.ι S.toCycles ≫ S.iCycles)
      (by simp)
  have : (kernel S.toCycles).IsQuasicoherent :=
    (Scheme.Modules.isQuasicoherent X).prop_of_iso eK.symm inferInstance
  have : (image S.toCycles).IsQuasicoherent :=
    (Scheme.Modules.isQuasicoherent X).prop_of_iso eI.symm inferInstance
  -- the kernel and the image of `S.toCycles` are quasi-coherent
  exact preservesLeftHomologyOf_sectionsFunctor S
    (Scheme.Modules.subsingleton_cohomology_succ_of_isAffine (kernel S.toCycles) 0)
    (Scheme.Modules.subsingleton_cohomology_succ_of_isAffine (image S.toCycles) 0)

section Complex

variable (K : CochainComplex X.Modules ℤ)

/-- **Acyclicity of cycles and boundaries.** If a complex `K` of `𝒪_X`-modules vanishes below some
degree, and its terms and its cohomology sheaves have no higher cohomology, then neither have its
sheaves of cycles `Zⁱ` nor its sheaves of boundaries, the images of `Kⁱ ⟶ Zⁱ⁺¹`. -/
theorem subsingleton_cohomology_cycles_and_image_toCycles (a : ℤ) [K.IsStrictlyGE a]
    (hX : ∀ i p, Subsingleton (Cohomology (K.X i) (p + 1)))
    (hH : ∀ i p, Subsingleton (Cohomology (K.homology i) (p + 1))) (i : ℤ) :
    (∀ p, Subsingleton (Cohomology (K.cycles i) (p + 1))) ∧
      ∀ j, i + 1 = j → ∀ p, Subsingleton (Cohomology (image (K.toCycles i j)) (p + 1)) := by
  -- the image of `Kⁱ ⟶ Zʲ` is acyclic as soon as the cycles `Zⁱ` are
  have himage (i j : ℤ) (hij : i + 1 = j) (hZ : ∀ p, Subsingleton (Cohomology (K.cycles i) (p + 1)))
      (p : ℕ) : Subsingleton (Cohomology (image (K.toCycles i j)) (p + 1)) := by
    have : Subsingleton (Cohomology (kernel (K.toCycles i j)) (p + 1 + 1)) :=
      have := hZ (p + 1)
      subsingleton_cohomology_of_iso (K.kernelToCyclesIso i j (by simpa using hij)).symm _
    exact subsingleton_cohomology_X₃
      (ShortComplex.exact_kernel (K.toCycles i j)).shortExact_factorThruImage
      (p + 1) (p + 1 + 1) rfl (hX i p) this
  -- below `a` everything vanishes
  have hzero (i : ℤ) (hi : i < a) (p : ℕ) : Subsingleton (Cohomology (K.cycles i) (p + 1)) :=
    subsingleton_cohomology_of_isZero
      ((K.isZero_of_isStrictlyGE a i hi).of_mono (K.iCycles i)) _
  suffices h : ∀ k : ℕ, ∀ p, Subsingleton (Cohomology (K.cycles (a - 1 + k)) (p + 1)) by
    have hZ (i : ℤ) : ∀ p, Subsingleton (Cohomology (K.cycles i) (p + 1)) := by
      by_cases hi : a - 1 ≤ i
      · obtain ⟨k, rfl⟩ : ∃ k : ℕ, i = a - 1 + k := ⟨(i - (a - 1)).toNat, by lia⟩
        exact h k
      · exact hzero i (by lia)
    exact ⟨hZ i, fun j hij ↦ himage i j hij (hZ i)⟩
  intro k
  induction k with
  | zero => exact hzero _ (by lia)
  | succ k ih =>
    rw [show a - 1 + ((k + 1 : ℕ) : ℤ) = a - 1 + k + 1 by push_cast; ring]
    set i := a - 1 + (k : ℤ)
    -- `0 ⟶ Bⁱ⁺¹ ⟶ Zⁱ⁺¹ ⟶ Hⁱ⁺¹ ⟶ 0`, with `Hⁱ⁺¹` the cokernel of `Kⁱ ⟶ Zⁱ⁺¹`
    intro p
    have e : cokernel (K.toCycles i (i + 1)) ≅ K.homology (i + 1) :=
      (cokernelIsCokernel _).coconePointUniqueUpToIso (K.homologyIsCokernel i (i + 1) (by simp))
    have : Subsingleton (Cohomology (cokernel (K.toCycles i (i + 1))) (p + 1)) :=
      have := hH (i + 1) p
      subsingleton_cohomology_of_iso e.symm _
    exact subsingleton_cohomology_X₂
      (ShortComplex.shortExact_image_ι_cokernel_π (K.toCycles i (i + 1))) (p + 1)
      (himage i (i + 1) rfl ih p) this

/-- **Global sections commute with the cohomology of bounded below acyclic complexes.** If a
complex `K` of `𝒪_X`-modules vanishes below some degree, and its terms and its cohomology sheaves
have no higher cohomology, then global sections preserve the homology of `K` in every degree `j`:
`Hʲ(Γ(X, K)) ≅ Γ(X, Hʲ(K))`, via `ShortComplex.mapHomologyIso`. -/
theorem preservesLeftHomologyOf_sectionsFunctor_sc (a : ℤ) [K.IsStrictlyGE a]
    (hX : ∀ i p, Subsingleton (Cohomology (K.X i) (p + 1)))
    (hH : ∀ i p, Subsingleton (Cohomology (K.homology i) (p + 1))) (j : ℤ) :
    (Scheme.Modules.sectionsFunctor (⊤ : X.Opens)).PreservesLeftHomologyOf (K.sc j) := by
  have h := subsingleton_cohomology_cycles_and_image_toCycles K a hX hH ((ComplexShape.up ℤ).prev j)
  have : Subsingleton (Cohomology (K.cycles ((ComplexShape.up ℤ).prev j)) (0 + 1)) := h.1 0
  exact preservesLeftHomologyOf_sectionsFunctor (K.sc j)
    (subsingleton_cohomology_of_iso (K.kernelToCyclesIso _ j (by simp)).symm _) (h.2 j (by simp) 0)

end Complex

section Local

/-- **Exactness is local on affine opens.** A complex of `𝒪_X`-modules is exact in degree `j` as
soon as the complexes of global sections of its restrictions to all affine opens are exact in
degree `j`. The converse fails: global sections are not exact. -/
theorem exactAt_of_forall_isAffineOpen (F : CochainComplex X.Modules ℤ) (j : ℤ)
    (h : ∀ U : X.Opens, IsAffineOpen U →
      (((Scheme.Modules.sectionsFunctor (⊤ : U.toScheme.Opens)).mapHomologicalComplex _).obj
        (((Scheme.Modules.restrictFunctor U.ι).mapHomologicalComplex _).obj F)).ExactAt j) :
    F.ExactAt j := by
  rw [HomologicalComplex.exactAt_iff' F (j - 1) j (j + 1) (by simp) (by simp)]
  refine (toSheaf X).reflects_exact_of_faithful _ (TopCat.Sheaf.exact_of_isBasis
    (B := {V | ∃ U : X.Opens, IsAffineOpen U ∧ U.ι ''ᵁ ⊤ = V}) ?_ ?_)
  · convert X.isBasis_affineOpens using 1
    ext V
    exact ⟨by rintro ⟨U, hU, rfl⟩; rwa [Scheme.Opens.ι_image_top], fun hV ↦ ⟨V, hV, by simp⟩⟩
  · rintro _ ⟨U, hU, rfl⟩ s hs
    have := h U hU
    rw [HomologicalComplex.exactAt_iff' _ (j - 1) j (j + 1) (by simp) (by simp),
      ShortComplex.moduleCat_exact_iff] at this
    -- the sections over `⊤` of the restriction to `U` are, by definition of restriction, the
    -- sections over the image of `⊤`, with the same maps
    exact this s hs


end Local

end TauCeti.AlgebraicGeometry.Scheme.Modules
