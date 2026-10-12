/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.Relative.Disk
public import TauCeti.AlgebraicTopology.Homotopy.Relative.Exact
public import TauCeti.Topology.Homotopy.HomotopyGroup.WeakHomotopyEquivalence
public import TauCeti.Topology.Homotopy.MappingCylinder

/-!
# Whitehead's theorem

**Whitehead's theorem** says that a weak homotopy equivalence between CW complexes is a homotopy
equivalence (Hatcher, *Algebraic Topology*, Theorem 4.5). This file proves it for Mathlib's
classical CW complexes, as `ContinuousMap.IsWeakHomotopyEquivalence.homotopyEquiv`, whose
forward map is the given weak homotopy equivalence.

The proof goes through Hatcher's Proposition 4.22: if `f : X → Y` is a weak homotopy equivalence,
then every map `g : K → Y` out of a CW complex `K` lifts through `f` up to homotopy
(`ContinuousMap.IsWeakHomotopyEquivalence.exists_comp_homotopic`).

* In the mapping cylinder `M_f`, which contains `X` as the bottom face `incl f` and deformation
  retracts onto `Y`, the relative homotopy groups `π_{n+1}(M_f, X, x)` all vanish
  (`ContinuousMap.IsWeakHomotopyEquivalence.subsingleton_relHomotopyGroup_mappingCylinder`). The
  inclusion `X ↪ M_f` composed with the retraction `M_f → Y` is `f`, so it induces bijections on
  all homotopy groups, and the exact sequence of the pair `(M_f, X)` does the rest
  (`TauCeti.RelHomotopyGroup.subsingleton_of_injective_of_surjective`).
* The compression lemma (`TauCeti.exists_homotopicRel_range_subset_of_relHomotopyGroup`) then
  deforms `K → Y ↪ M_f` into `X`, and retracting back to `Y` gives the lift.

Applied to the identity of `Y`, when `Y` is a CW complex, the lift is a map `g : Y → X` with
`f ∘ g ≃ id`. By two out of three, `g` is again a weak homotopy equivalence, so when `X` is a CW
complex `g` has a right homotopy inverse `h` in turn. Then `f ≃ f ∘ g ∘ h ≃ h`, and so
`g ∘ f ≃ g ∘ h ≃ id`. Unlike Hatcher's proof of Theorem 4.5, this argument needs neither a CW
structure on the mapping cylinder nor cellular approximation: the only cell-by-cell argument is
the skeletal induction inside the compression lemma.

## Main declarations

* `ContinuousMap.IsWeakHomotopyEquivalence.subsingleton_relHomotopyGroup_mappingCylinder`: the
  relative homotopy groups of the mapping cylinder of a weak homotopy equivalence vanish.
* `ContinuousMap.IsWeakHomotopyEquivalence.exists_comp_homotopic`: maps out of CW complexes lift
  through a weak homotopy equivalence up to homotopy.
* `ContinuousMap.IsWeakHomotopyEquivalence.homotopyEquiv`: **Whitehead's theorem**.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 4.1, Theorem 4.5 (Whitehead's theorem), Lemma 4.6 (the compression lemma), and
  Proposition 4.22.
-/

public section

universe w

open Set Topology Topology.RelCWComplex

namespace ContinuousMap.IsWeakHomotopyEquivalence

variable {X : Type*} [TopologicalSpace X] {Y : Type*} [TopologicalSpace Y] {f : C(X, Y)}

/-- The relative homotopy groups `π_{n+1}(M_f, X, x)` of the mapping cylinder of a weak homotopy
equivalence `f : X → Y`, relative to its bottom face `X`, are trivial at every basepoint of the
bottom face. -/
theorem subsingleton_relHomotopyGroup_mappingCylinder (hf : f.IsWeakHomotopyEquivalence)
    (N : Type w) [Finite N] (b : range (TauCeti.MappingCylinder.incl f)) :
    Subsingleton (TauCeti.RelHomotopyGroup N
      ⟨TopPair.ofSubset (X := TopCat.of (TauCeti.MappingCylinder f))
        (range (TauCeti.MappingCylinder.incl f)), b⟩) := by
  open TauCeti.MappingCylinder in
  let ψ := (isClosedEmbedding_incl (f := f)).isEmbedding.toHomeomorph
  obtain ⟨x, rfl⟩ := ψ.surjective b
  -- The inclusion `ι` of the bottom face, composed with `ψ : X ≃ₜ range (incl f)` and with the
  -- projection `M_f → Y`, is `f`; the outer two maps are homotopy equivalences.
  let ι := (TopPair.ofSubset (X := TopCat.of (TauCeti.MappingCylinder f))
    (range (incl f))).map.hom
  have hcomp : (proj f).comp (ι.comp (ψ : C(X, range (incl f)))) = f := by
    ext x'
    -- `ι` is `Subtype.val`, and `ψ x'` is `incl f x'` as a point of `range (incl f)`.
    exact (congrArg (proj f) (IsEmbedding.toHomeomorph_apply_coe
      (isClosedEmbedding_incl (f := f)).isEmbedding x')).trans
      (DFunLike.congr_fun (proj_comp_incl (f := f)) x')
  have hproj : (homotopyEquiv f).toFun = proj f := ContinuousMap.ext homotopyEquiv_apply
  have hι (M : Type w) [Finite M] :
      Function.Bijective (HomotopyGroup.map (N := M) (x := ψ x) ι rfl) := by
    have hfun : HomotopyGroup.map (N := M) (proj f) rfl ∘ HomotopyGroup.map ι rfl ∘
        HomotopyGroup.map (ψ : C(X, range (incl f))) rfl =
          HomotopyGroup.map f (DFunLike.congr_fun hcomp x).symm := by
      funext a
      exact ((congrArg _ (HomotopyGroup.map_comp_apply ι rfl _ rfl a)).trans
        (HomotopyGroup.map_comp_apply _ rfl _ rfl a)).trans (HomotopyGroup.map_congr hcomp _ _ a)
    have h : ∀ {y : Y} (hy : f x = y), Function.Bijective (HomotopyGroup.map (N := M) f hy) := by
      rintro _ rfl
      exact hf.map_bijective M x
    have hcyl : Function.Bijective
        (HomotopyGroup.map (N := M) (proj f) (rfl : proj f (ι (ψ x)) = _)) := by
      rw [← hproj]
      exact HomotopyGroup.map_bijective_of_homotopyEquiv _ _
    have hψ := HomotopyGroup.map_bijective_of_homotopyEquiv (N := M) ψ.toHomotopyEquiv x
    have h' := h (DFunLike.congr_fun hcomp x).symm
    rw [← hfun] at h'
    exact (Function.Bijective.of_comp_iff _ hψ).1 ((Function.Bijective.of_comp_iff' hcyl _).1 h')
  exact TauCeti.RelHomotopyGroup.subsingleton_of_injective_of_surjective (hι N).injective
    (hι (Option N)).surjective

variable {X' : Type*} [TopologicalSpace X'] [T2Space X'] {C : Set X'} [CWComplex C]

/-- **Maps out of a CW complex lift through a weak homotopy equivalence up to homotopy**
(Hatcher, Proposition 4.22). If `f : X → Y` is a weak homotopy equivalence and `C` is a CW
complex, then every map `g : C → Y` is homotopic to `f ∘ g'` for some `g' : C → X`. -/
theorem exists_comp_homotopic (hf : f.IsWeakHomotopyEquivalence) (g : C(C, Y)) :
    ∃ g' : C(C, X), (f.comp g').Homotopic g := by
  open TauCeti TauCeti.MappingCylinder in
  -- Every point `m` of the mapping cylinder is joined by a path to the bottom face: the
  -- deformation onto the base joins `m` to `mkBase (proj m)`, and `incl x` to `mkBase (f x)`.
  have hdef (m : MappingCylinder f) : Joined m (mkBase f (proj f m)) :=
    ⟨(deformation f).toHomotopy.evalAt m⟩
  have h₀ (m : MappingCylinder f) : ∃ b ∈ range (incl f), Joined m b := by
    obtain ⟨x, hx⟩ := hf.exists_joined (proj f m)
    have hx' := hdef (incl f x)
    rw [← ContinuousMap.comp_apply (proj f), proj_comp_incl] at hx'
    exact ⟨incl f x, mem_range_self x,
      (hdef m).trans ((hx.symm.map (mkBase f).continuous).trans hx'.symm)⟩
  -- Compress `mkBase f ∘ g : C → M_f` into the bottom face `range (incl f)`.
  obtain ⟨g₁, hg₁, hrange⟩ := exists_homotopicRel_range_subset_of_relHomotopyGroup
    (C := C) (D := ∅) (Y := TopCat.of (MappingCylinder f)) (B := range (incl f)) (fun _ ↦ h₀)
    (fun _ _ b ↦ hf.subsingleton_relHomotopyGroup_mappingCylinder _ b) ((mkBase f).comp g)
    (fun _ hx ↦ absurd hx (notMem_empty _))
  -- Read the compressed map in `X` through the homeomorphism `X ≃ₜ range (incl f)`.
  let ψ := (isClosedEmbedding_incl (f := f)).isEmbedding.toHomeomorph
  let g' : C(C, X) := (ψ.symm : C(range (incl f), X)).comp
    ⟨fun c ↦ (⟨g₁ c, hrange (mem_range_self c)⟩ : range (incl f)), g₁.continuous.subtype_mk _⟩
  have hg' : (incl f).comp g' = g₁ := by
    ext c
    rw [ContinuousMap.comp_apply,
      ← IsEmbedding.toHomeomorph_apply_coe (isClosedEmbedding_incl (f := f)).isEmbedding]
    exact congrArg Subtype.val (ψ.apply_symm_apply ⟨g₁ c, hrange (mem_range_self c)⟩)
  -- Then `f ∘ g' = proj ∘ incl ∘ g' = proj ∘ g₁ ≃ proj ∘ mkBase ∘ g = g`.
  refine ⟨g', ?_⟩
  have h := (ContinuousMap.Homotopic.refl (proj f)).comp hg₁.homotopic.symm
  rwa [← comp_assoc, proj_comp_mkBase, id_comp, ← hg', ← comp_assoc, proj_comp_incl] at h

variable {Y' : Type*} [TopologicalSpace Y'] [T2Space Y'] {D : Set Y'} [CWComplex D]
  {f : C(C, D)}

/-- **Whitehead's theorem** (Hatcher, Theorem 4.5). A weak homotopy equivalence `f` between CW
complexes is a homotopy equivalence. This is the homotopy equivalence whose forward map is `f`
itself (`ContinuousMap.IsWeakHomotopyEquivalence.homotopyEquiv_toFun`); its homotopy inverse is a
lift of the identity through `f` given by
`ContinuousMap.IsWeakHomotopyEquivalence.exists_comp_homotopic`. -/
noncomputable def homotopyEquiv (hf : f.IsWeakHomotopyEquivalence) : C ≃ₕ D :=
  have hfg := (hf.exists_comp_homotopic (ContinuousMap.id D)).choose_spec
  { toFun := f
    invFun := (hf.exists_comp_homotopic (ContinuousMap.id D)).choose
    left_inv := by
      -- The homotopy inverse `g` is a weak homotopy equivalence by two out of three, so it has a
      -- right homotopy inverse `h`; then `f ≃ f ∘ g ∘ h ≃ h` and `g ∘ f ≃ g ∘ h ≃ id`.
      set g := (hf.exists_comp_homotopic (ContinuousMap.id D)).choose
      obtain ⟨h, hgh⟩ := (hf.of_comp (IsWeakHomotopyEquivalence.id.of_homotopic hfg.symm))
        |>.exists_comp_homotopic (ContinuousMap.id C)
      have hfh : f.Homotopic h := by
        have := (ContinuousMap.Homotopic.refl f).comp hgh.symm
        have hfgh := hfg.comp (ContinuousMap.Homotopic.refl h)
        rw [comp_id, ← comp_assoc] at this
        rw [id_comp] at hfgh
        exact this.trans hfgh
      exact ((ContinuousMap.Homotopic.refl g).comp hfh).trans hgh
    right_inv := hfg }

@[simp]
theorem homotopyEquiv_toFun (hf : f.IsWeakHomotopyEquivalence) : hf.homotopyEquiv.toFun = f :=
  (rfl)

end ContinuousMap.IsWeakHomotopyEquivalence
