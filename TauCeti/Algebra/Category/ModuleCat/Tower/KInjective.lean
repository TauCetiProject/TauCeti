/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.QuasiIso
public import TauCeti.Algebra.Category.ModuleCat.Tower.Milnor
public import TauCeti.Algebra.Category.ModuleCat.Tower.Tail
public import TauCeti.Algebra.Homology.HomotopyCategory.KInjective

/-!
# Limits of towers of complexes of modules as K-injective replacements

Let `C₀ ← C₁ ← C₂ ← ⋯` be a tower of cochain complexes of `R`-modules indexed by `ℤ`. If every
`Cₙ` is K-injective and every transition chain map `Cₙ₊₁ → Cₙ` is a split epimorphism in each
degree, then the limit complex `lim C` is K-injective
(`TauCeti.ComplexTower.isKInjective_limComplex`). The proof uses the sequence
`0 → lim C → ∏ₙ Cₙ → ∏ₙ Cₙ → 0` formed by the inclusion and the shift `δ(x)ₙ = xₙ - φₙ(xₙ₊₁)`
(`TauCeti.ComplexTower.shortComplex`). The product complex is K-injective as a product of
K-injective complexes, and when the transitions are split in each degree, so is the shift, so this
sequence is split short exact in every degree. The first term of such a sequence with K-injective
second and third terms is K-injective.

On the homology side, if a cone over a tower of complexes with surjective shift maps has legs that,
in each degree, induce isomorphisms on homology for all sufficiently large `n`, then the induced
map into the limit complex is a quasi-isomorphism
(`TauCeti.ComplexTower.quasiIso_isLimitLimComplexCone_lift`): the towers of homology modules are
eventually constant, so the `lim¹` term of the Milnor sequence vanishes.

Together these are the limit step of Spaltenstein's construction of K-injective replacements of
unbounded complexes of modules: a replacement of a complex `K` is the limit of a tower of
K-injective replacements of the truncations `τ^{≥ -n} K`, chosen with degreewise split surjective
transitions. In degree `j`, the truncation map `K → τ^{≥ -n} K` induces an isomorphism on
homology as soon as `-n ≤ j`.

## Main declarations

* `TauCeti.ComplexTower.isKInjective_productComplex`: the product complex of a tower of
  K-injective complexes is K-injective.
* `TauCeti.ComplexTower.isKInjective_limComplex`: the limit complex of a tower of K-injective
  complexes with degreewise split epimorphic transitions is K-injective.
* `TauCeti.ComplexTower.quasiIso_isLimitLimComplexCone_lift`: a cone whose legs are eventually
  isomorphisms on homology in each degree induces a quasi-isomorphism into the limit complex.

## References

* N. Spaltenstein, *Resolutions of unbounded complexes*, Compositio Math. 65 (1988), 121–154.
* Stacks Project, *Derived Categories*, the section on K-injective complexes.
-/

public section

namespace TauCeti

namespace ComplexTower

open CategoryTheory Limits Opposite

universe v u

variable {R : Type u} [Ring R] (C : ComplexTower.{v} R (ComplexShape.up ℤ))

/-- The product complex of a tower of K-injective cochain complexes of modules is K-injective. -/
theorem isKInjective_productComplex [∀ n, CochainComplex.IsKInjective (C.obj (op n))] :
    CochainComplex.IsKInjective C.productComplex :=
  CochainComplex.isKInjective_of_isLimit_fan C.isLimitProductComplexFan

/-- **Limits of towers of K-injective complexes.** If every complex of a tower of cochain
complexes of modules is K-injective, and every transition chain map `Cₙ₊₁ → Cₙ` is a split
epimorphism in each degree, then the limit complex of the tower is K-injective. -/
theorem isKInjective_limComplex [∀ n, CochainComplex.IsKInjective (C.obj (op n))]
    (hC : ∀ (n : ℕ) (p : ℤ), IsSplitEpi ((C.map (homOfLE (Nat.le_succ n)).op).f p)) :
    CochainComplex.IsKInjective C.limComplex := by
  have : CochainComplex.IsKInjective C.shortComplex.X₂ := C.isKInjective_productComplex
  have : CochainComplex.IsKInjective C.shortComplex.X₃ := C.isKInjective_productComplex
  -- In each degree, the sequence `lim → ∏ → ∏` is exact with injective first map, and the shift
  -- has a section, so it splits.
  let S (p : ℤ) := C.shortComplex.map (HomologicalComplex.eval _ _ p)
  have hf (p : ℤ) : (S p).f = ModuleCat.ofHom (C.term p).lim.subtype :=
    ModuleCat.hom_ext (C.limComplexι_f_hom p)
  have hg (p : ℤ) : (S p).g = ModuleCat.ofHom (C.term p).shift :=
    ModuleCat.hom_ext (C.productComplexShift_f_hom p)
  have hexact (p : ℤ) : (S p).Exact := by
    rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact, hf, hg]
    exact ModuleTower.exact_lim_subtype_shift (C.term p)
  have hmono (p : ℤ) : Mono (S p).f :=
    (ModuleCat.mono_iff_injective _).2 (by rw [hf]; exact (C.term p).lim.injective_subtype)
  have hδ (p : ℤ) : IsSplitEpi (ModuleCat.ofHom (C.term p).shift) :=
    (C.term p).isSplitEpi_shift fun n ↦ hC n p
  exact CochainComplex.isKInjective_X₁_of_degreewiseSplit C.shortComplex fun p ↦
    ShortComplex.Splitting.ofExactOfSection (S p) (hexact p) (hδ p).exists_splitEpi.some.section_
      (by rw [hg]; exact (hδ p).exists_splitEpi.some.id) (hmono p)

section QuasiIso

variable {ι : Type*} {c : ComplexShape ι} {C : ComplexTower.{v} R c}

/-- The maps induced on homology by the legs of a cone over a tower of complexes are compatible
with the transitions of the tower of homology modules. -/
theorem transition_comp_homologyMap_π (s : Cone C) (j : ι) (n : ℕ) :
    (C.homology j).transition n ∘ₗ (HomologicalComplex.homologyMap (s.π.app (op (n + 1))) j).hom =
      (HomologicalComplex.homologyMap (s.π.app (op n)) j).hom := by
  rw [homology_transition]
  exact congrArg ModuleCat.Hom.hom ((HomologicalComplex.homologyMap_comp _ _ j).symm.trans
    (congrArg (HomologicalComplex.homologyMap · j) (s.w (homOfLE (Nat.le_succ n)).op)))

/-- **Quasi-isomorphisms into the limit of a tower of complexes.** Let `C` be a tower of complexes
whose shift is surjective in every degree, for instance one whose transitions are surjective in
every degree, and in which every degree `j` receives a differential from some degree `i`. If `s` is
a cone over `C` whose legs `s.pt → Cₙ` induce isomorphisms on the degree-`j` homology for all
sufficiently large `n`, for every `j`, then the induced map from `s.pt` to the limit complex is a
quasi-isomorphism. -/
theorem quasiIso_isLimitLimComplexCone_lift (hC : ∀ i, Function.Surjective (C.term i).shift)
    (hc : ∀ j, ∃ i, c.Rel i j) (s : Cone C)
    (hs : ∀ j, ∃ N, ∀ n, N ≤ n → QuasiIsoAt (s.π.app (op n)) j) :
    QuasiIso (C.isLimitLimComplexCone.lift s) := by
  let φ : s.pt ⟶ C.limComplex := C.isLimitLimComplexCone.lift s
  have hφ (n : ℕ) : φ ≫ C.limComplexπ n = s.π.app (op n) := C.isLimitLimComplexCone.fac s (op n)
  have hbij (j : ι) (n : ℕ) (h : QuasiIsoAt (s.π.app (op n)) j) :
      Function.Bijective (HomologicalComplex.homologyMap (s.π.app (op n)) j).hom :=
    (ConcreteCategory.isIso_iff_bijective _).1 ((quasiIsoAt_iff_isIso_homologyMap _ _).1 h)
  rw [quasiIso_iff]
  intro j
  rw [quasiIsoAt_iff_isIso_homologyMap, ConcreteCategory.isIso_iff_bijective]
  obtain ⟨i, hij⟩ := hc j
  -- The tower of degree-`i` homology modules has eventually surjective transitions, so its `lim¹`
  -- vanishes and the Milnor map `Hⱼ(lim C) → lim Hⱼ(Cₙ)` is bijective.
  have : Subsingleton (C.homology i).limOne := by
    obtain ⟨N, hN⟩ := hs i
    refine (C.homology i).subsingleton_limOne_of_surjective_of_le N fun n hn y ↦ ?_
    obtain ⟨x, hx⟩ := (hbij i n (hN n hn)).2 y
    exact ⟨_, (LinearMap.congr_fun (transition_comp_homologyMap_π s i n) x).trans hx⟩
  -- Composed with the Milnor map, the map on homology is the map induced by the legs of `s`.
  let f (n : ℕ) : s.pt.homology j →ₗ[R] (C.homology j).obj (op n) :=
    (HomologicalComplex.homologyMap (s.π.app (op n)) j).hom
  have hcomp : C.homologyToLim j ∘ₗ (HomologicalComplex.homologyMap φ j).hom =
      (C.homology j).limLift f (transition_comp_homologyMap_π s j) := by
    refine (C.homology j).lim_hom_ext fun n ↦ LinearMap.ext fun x ↦ ?_
    rw [ModuleTower.limπ_comp_limLift, LinearMap.comp_apply, LinearMap.comp_apply,
      ModuleTower.limπ_apply, coe_homologyToLim_apply]
    have h := congrArg (fun g : s.pt ⟶ C.obj (op n) ↦ (HomologicalComplex.homologyMap g j).hom x)
      (hφ n)
    simp only [HomologicalComplex.homologyMap_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at h
    exact h
  obtain ⟨N, hN⟩ := hs j
  have h := (C.homology j).limLift_bijective_of_le f (transition_comp_homologyMap_π s j) N
    fun n hn ↦ hbij j n (hN n hn)
  rw [← hcomp, LinearMap.coe_comp] at h
  exact ((homologyToLim_bijective hC hij).of_comp_iff' _).1 h

end QuasiIso

end ComplexTower

end TauCeti
