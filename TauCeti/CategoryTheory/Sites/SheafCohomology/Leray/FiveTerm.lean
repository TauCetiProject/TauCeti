/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.SheafCohomology.Leray.Edge

/-!
# The first terms of the five-term exact sequence of the Leray spectral sequence

Let `pb : Sheaf J Ab ⥤ Sheaf K Ab` be an exact functor between categories of abelian sheaves on
sites `(C, J)` and `(D, K)` with right adjoint `pf`, and `c : ℤ_K ⟶ pb ℤ_J` an isomorphism of
constant sheaves; for a morphism of sites, `pb = f⁻¹`, `pf = f_*`. The Leray spectral sequence
`E₂^{p,q} = Hᵖ(C, R^q f_* F) ⇒ H^{p+q}(D, F)` (Stacks, Lemma 21.14.5 (0732)) has the five-term
exact sequence

`0 ⟶ H¹(C, f_* F) ⟶ H¹(D, F) ⟶ H⁰(C, R¹ f_* F) ⟶ H²(C, f_* F) ⟶ H²(D, F)`.

This file constructs a map `H¹(D, F) ⟶ H⁰(C, R¹ f_* F)` in the place of its third map and proves
exactness at `H¹(D, F)`, independently of spectral-sequence machinery. The first map is the edge
map `Sheaf.H.lerayEdge`, injective in degree one (`Sheaf.H.lerayEdge_one_injective`).

The map is defined using a chosen short exact sequence `0 ⟶ F ⟶ I ⟶ Q ⟶ 0` with `I` injective.
Then `H¹(I) = 0`, so every class of `H¹(D, F)` is `δ y` for a section `y` of `Q`, and `R¹ f_* F`
is the cokernel of `f_* I ⟶ f_* Q` (`Functor.rightDerivedOneIsoCokernel`, for any left exact
functor). The map sends `δ y` to the image in the cokernel of `y`, read as a section of `f_* Q`
(`Sheaf.H.lerayFiveTermMap`). Its independence of `I` and its agreement with the map of the
spectral sequence are not proved here. Exactness at `H¹(D, F)` uses the short exact sequences
`0 ⟶ f_* F ⟶ f_* I ⟶ f_* I / f_* F ⟶ 0` and
`0 ⟶ f_* I / f_* F ⟶ f_* Q ⟶ coker (f_* I ⟶ f_* Q) ⟶ 0` on `C`, the second from left exactness of
`f_*` (`Functor.shortExact_cokernelMapFToMapX₃`), and the compatibility of the edge map with the
connecting maps (`Sheaf.H.lerayEdge_one_δ_cokernelSequence`).

For a morphism of sites given by `u : C ⥤ D`, with the hypotheses of
`Sheaf.H.lerayEdge_sheafAdjunctionContinuous_bijective`, these results apply to
`adj := u.sheafAdjunctionContinuous AddCommGrpCat J K` and
`c := (u.sheafPullbackConstantSheafIso AddCommGrpCat J K (of (ULift ℤ))).inv`; then `R¹ f_*` is
the higher direct image `u.sheafHigherDirectImage AddCommGrpCat J K 1`.

## Main declarations

* `CategoryTheory.Sheaf.H.lerayFiveTermMap`: a map `H¹(D, F) →+ H⁰(C, R¹ f_* F)`, defined using
  the chosen injective `I`.
* `CategoryTheory.Sheaf.H.exact_lerayEdge_one_lerayFiveTermMap`: exactness of
  `H¹(C, f_* F) ⟶ H¹(D, F) ⟶ H⁰(C, R¹ f_* F)` at `H¹(D, F)`.

## References

* [The Stacks Project, Section 21.14](https://stacks.math.columbia.edu/tag/072X), especially
  Tag 0732.
-/

public section

open CategoryTheory Abelian Limits

namespace CategoryTheory.Sheaf.H

open AddCommGrpCat

universe w w₁ w₂

variable {C : Type*} [Category* C] {J : GrothendieckTopology C}
  {D : Type*} [Category* D] {K : GrothendieckTopology D}
  [HasSheafify J AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w}]
  [HasExt.{w₁} (Sheaf J AddCommGrpCat.{w})] [HasExt.{w₂} (Sheaf K AddCommGrpCat.{w})]
  {pb : Sheaf J AddCommGrpCat.{w} ⥤ Sheaf K AddCommGrpCat.{w}} [pb.Additive]
  [PreservesFiniteLimits pb] [PreservesFiniteColimits pb]
  {pf : Sheaf K AddCommGrpCat.{w} ⥤ Sheaf J AddCommGrpCat.{w}} [pf.Additive]
  [PreservesFiniteLimits pf] (adj : pb ⊣ pf)
  (c : (constantSheaf K AddCommGrpCat.{w}).obj (of (ULift ℤ)) ⟶
    pb.obj ((constantSheaf J AddCommGrpCat.{w}).obj (of (ULift ℤ))))
  {S : ShortComplex (Sheaf K AddCommGrpCat.{w})} (hS : S.ShortExact)

noncomputable section

variable [IsIso c]

/-- For a short complex `F ⟶ I ⟶ Q`, the map
`H⁰(D, Q) ≅ H⁰(C, f_* Q) ⟶ H⁰(C, coker (f_* I ⟶ f_* Q))`, through the inverse of the edge map in
degree zero. -/
def lerayFiveTermAux : H S.X₃ 0 →+ H (cokernel (pf.map S.g)) 0 :=
  (H.map (cokernel.π (pf.map S.g)) 0).comp (lerayEdgeZeroEquiv adj c S.X₃).symm.toAddMonoidHom

omit [pf.Additive] [PreservesFiniteLimits pf] in
/-- `lerayFiveTermAux` sends the edge-map image of a section `x` of `f_* Q` to the image of `x` in
`coker (f_* I ⟶ f_* Q)`. -/
@[simp]
lemma lerayFiveTermAux_lerayEdge (x : H (pf.obj S.X₃) 0) :
    lerayFiveTermAux adj c (lerayEdge adj c S.X₃ 0 x) = H.map (cokernel.π (pf.map S.g)) 0 x := by
  simp [lerayFiveTermAux]

include hS in
/-- `lerayFiveTermAux` kills the image of `H⁰(D, I) ⟶ H⁰(D, Q)`, the kernel of
`δ : H⁰(D, Q) ⟶ H¹(D, F)`. -/
lemma ker_δ_le_ker_lerayFiveTermAux :
    (H.δ hS 0 1 rfl).ker ≤ (lerayFiveTermAux adj c (S := S)).ker := by
  intro y hy
  obtain ⟨z, rfl⟩ := (exact_map_δ hS 0 1 rfl y).1 hy
  obtain ⟨w, rfl⟩ := (lerayEdge_zero_bijective adj c S.X₂).2 z
  rw [AddMonoidHom.mem_ker, ← lerayEdge_naturality, lerayFiveTermAux_lerayEdge]
  simpa only [← H.map_comp_apply, Functor.π_cokernelMapFToMapX₃] using
    (exact_map_map (pf.shortExact_cokernelMapFToMapX₃ hS) 0).apply_apply_eq_zero
      (H.map (cokernel.π (pf.map S.f)) 0 w)

variable [Injective S.X₂]

/-- A map `H¹(D, F) ⟶ H⁰(C, coker (f_* I ⟶ f_* Q))`, defined using the chosen short exact
sequence `0 ⟶ F ⟶ I ⟶ Q ⟶ 0` with `I` injective: every class of `H¹(D, F)` is `δ y` for a section
`y` of `Q`, sent to the image of `y` in the cokernel. -/
def lerayFiveTermCokernelMap : H S.X₁ 1 →+ H (cokernel (pf.map S.g)) 0 :=
  (H.δ hS 0 1 rfl).liftOfSurjective (δ_surjective hS 0 1 rfl inferInstance)
    ⟨lerayFiveTermAux adj c, ker_δ_le_ker_lerayFiveTermAux adj c hS⟩

/-- `lerayFiveTermCokernelMap` sends `δ y`, for a section `y` of `Q`, to the image of `y` in
`H⁰(C, coker (f_* I ⟶ f_* Q))`. -/
@[simp]
lemma lerayFiveTermCokernelMap_δ (y : H S.X₃ 0) :
    lerayFiveTermCokernelMap adj c hS (H.δ hS 0 1 rfl y) = lerayFiveTermAux adj c y :=
  AddMonoidHom.liftOfRightInverse_comp_apply _ _ _ _ y

/-- **Exactness of `H¹(C, f_* F) ⟶ H¹(D, F) ⟶ H⁰(C, coker (f_* I ⟶ f_* Q))` at `H¹(D, F)`.** -/
theorem exact_lerayEdge_one_lerayFiveTermCokernelMap :
    Function.Exact (lerayEdge adj c S.X₁ 1) (lerayFiveTermCokernelMap adj c hS) := by
  have := hS.mono_f
  intro x
  constructor
  · intro hx
    obtain ⟨y, rfl⟩ := δ_surjective hS 0 1 rfl inferInstance x
    rw [lerayFiveTermCokernelMap_δ, lerayFiveTermAux, AddMonoidHom.comp_apply] at hx
    obtain ⟨v, hv⟩ := (exact_map_map (pf.shortExact_cokernelMapFToMapX₃ hS) 0 _).1 hx
    refine ⟨H.δ (TauCeti.cokernelSequence_shortExact (pf.map S.f)) 0 1 rfl v, ?_⟩
    rw [lerayEdge_one_δ_cokernelSequence adj c hS, hv, AddEquiv.coe_toAddMonoidHom,
      lerayEdge_lerayEdgeZeroEquiv_symm]
  · rintro ⟨x, rfl⟩
    have := subsingleton_H_succ_obj_of_injective adj S.X₂ 0
    obtain ⟨v, rfl⟩ :=
      δ_surjective (TauCeti.cokernelSequence_shortExact (pf.map S.f)) 0 1 rfl this x
    rw [lerayEdge_one_δ_cokernelSequence adj c hS v, lerayFiveTermCokernelMap_δ,
      lerayFiveTermAux_lerayEdge]
    exact (exact_map_map (pf.shortExact_cokernelMapFToMapX₃ hS) 0).apply_apply_eq_zero v

variable [EnoughInjectives (Sheaf K AddCommGrpCat.{w})]

/-- **A map `H¹(D, F) ⟶ H⁰(C, R¹ f_* F)` for the five-term exact sequence** of the Leray spectral
sequence, defined using the chosen short exact sequence `0 ⟶ F ⟶ I ⟶ Q ⟶ 0` with `I` injective:
the map `lerayFiveTermCokernelMap` to `H⁰(C, coker (f_* I ⟶ f_* Q))` followed by the identification
`coker (f_* I ⟶ f_* Q) ≅ R¹ f_* F` (`Functor.rightDerivedOneIsoCokernel`). Its independence of `I`
and its agreement with the map of the spectral sequence are not proved here. -/
def lerayFiveTermMap : H S.X₁ 1 →+ H ((pf.rightDerived 1).obj S.X₁) 0 :=
  (H.map (pf.rightDerivedOneIsoCokernel hS).inv 0).comp (lerayFiveTermCokernelMap adj c hS)

/-- `lerayFiveTermMap` sends `δ y`, for a section `y` of `Q`, to the image of `y` in
`H⁰(C, coker (f_* I ⟶ f_* Q)) ≅ H⁰(C, R¹ f_* F)`. -/
@[simp]
lemma lerayFiveTermMap_δ (y : H S.X₃ 0) :
    lerayFiveTermMap adj c hS (H.δ hS 0 1 rfl y) =
      H.map (pf.rightDerivedOneIsoCokernel hS).inv 0 (lerayFiveTermAux adj c y) := by
  rw [lerayFiveTermMap, AddMonoidHom.comp_apply, lerayFiveTermCokernelMap_δ]

/-- **Exactness of `H¹(C, f_* F) ⟶ H¹(D, F) ⟶ H⁰(C, R¹ f_* F)` at `H¹(D, F)`**, when the
comparison `c` of constant sheaves is an isomorphism: the image of the edge map is the kernel of
`lerayFiveTermMap`. With `lerayEdge_one_injective`, this gives the exact sequence
`0 ⟶ H¹(C, f_* F) ⟶ H¹(D, F) ⟶ H⁰(C, R¹ f_* F)`. -/
theorem exact_lerayEdge_one_lerayFiveTermMap :
    Function.Exact (lerayEdge adj c S.X₁ 1) (lerayFiveTermMap adj c hS) :=
  (exact_lerayEdge_one_lerayFiveTermCokernelMap adj c hS).comp_injective _
    (H.map_injective (pf.rightDerivedOneIsoCokernel hS).inv) (map_zero _)

end

end CategoryTheory.Sheaf.H
