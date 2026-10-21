/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.LineBundle.Basic
public import TauCeti.AlgebraicGeometry.Modules.Stalk

/-!
# Stalks of invertible sheaves

The stalk of an invertible sheaf `M` on a scheme `X` at a point `x` is free of rank one over the
local ring `𝒪_{X,x}`: the germ of the basis section of a rank-one trivialization near `x` is a
basis. This is the pointwise form of local freeness used to read off local generators of a line
bundle, for instance of the sheaf of differentials of a smooth curve.

## Main results

* `AlgebraicGeometry.Scheme.Modules.nonempty_linearEquiv_stalk_of_isInvertible`: the stalk of an
  invertible sheaf is isomorphic to the local ring as a module over it;
* `AlgebraicGeometry.Scheme.Modules.free_stalk_of_isInvertible` and
  `AlgebraicGeometry.Scheme.Modules.finrank_stalk_of_isInvertible`: the stalk is free of rank one.
* `AlgebraicGeometry.Scheme.Modules.span_germ_trivializationGenerator`: the germ of the basis
  section of a rank-one trivialization generates the stalk.
* `AlgebraicGeometry.Scheme.Modules.bijective_toSpanSingleton_of_span_eq_top`: every generator
  of the stalk of an invertible sheaf is a basis of it, and
  `AlgebraicGeometry.Scheme.Modules.span_smul_eq_top_iff`: a multiple `a • g` generates the stalk
  exactly when `a` is a unit and `g` generates.
-/

public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

universe u

variable {X : Scheme.{u}} (M : X.Modules)
  [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X M] (x : X)

omit [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X M] in
/-- The germ of the basis section of a rank-one trivialization generates the stalk: every germ of
a section of `M` is a germ of a regular function times it. -/
theorem span_germ_trivializationGenerator {V : X.Opens}
    (t : SheafOfModules.free (R := X.ringCatSheaf.over V) PUnit ≅ M.over V) (hxV : x ∈ V) :
    Submodule.span (X.presheaf.stalk x) {M.presheaf.germ V x hxV (trivializationGenerator M t)} =
      ⊤ := by
  refine (Submodule.span_singleton_eq_top_iff _ _).mpr fun m ↦ ?_
  obtain ⟨W, hxW, s, rfl⟩ := M.presheaf.exists_germ_eq m
  have hxWV : x ∈ W ⊓ V := Opens.mem_inf.mpr ⟨hxW, hxV⟩
  let i : W ⊓ V ⟶ V := homOfLE inf_le_right
  let j : W ⊓ V ⟶ W := homOfLE inf_le_left
  refine ⟨X.presheaf.germ (W ⊓ V) x hxWV
    (trivializationCoordinate M t i (M.presheaf.map j.op s)), ?_⟩
  rw [← TopCat.Presheaf.germ_res_apply M.presheaf i _ hxWV, ← germ_smul,
    ← eq_trivializationCoordinate_smul_map_trivializationGenerator,
    TopCat.Presheaf.germ_res_apply]

/-- **The stalk of an invertible sheaf is free of rank one.** The stalk `M_x` of an invertible
sheaf is isomorphic to the local ring `𝒪_{X,x}` as a module over it. -/
theorem nonempty_linearEquiv_stalk_of_isInvertible :
    Nonempty (X.presheaf.stalk x ≃ₗ[X.presheaf.stalk x] M.presheaf.stalk x) := by
  obtain ⟨V, t, hxV⟩ := exists_mem_trivialization M x
  let g := M.presheaf.germ V x hxV (trivializationGenerator M t)
  -- The germ of a section over `W ≤ V` is its coordinate's germ times `g`.
  have hgerm {W : X.Opens} (i : W ⟶ V) (hxW : x ∈ W) (s : Γ(M, W)) :
      M.presheaf.germ W x hxW s =
        X.presheaf.germ W x hxW (trivializationCoordinate M t i s) • g := by
    conv_lhs => rw [eq_trivializationCoordinate_smul_map_trivializationGenerator M t i s]
    rw [germ_smul, TopCat.Presheaf.germ_res_apply]
  refine ⟨LinearEquiv.ofBijective (LinearMap.toSpanSingleton _ _ g) ⟨?_, ?_⟩⟩
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro r hr
    obtain ⟨W, hxW, c, rfl⟩ := X.presheaf.exists_germ_eq r
    have hxWV : x ∈ W ⊓ V := Opens.mem_inf.mpr ⟨hxW, hxV⟩
    let i : W ⊓ V ⟶ V := homOfLE inf_le_right
    let j : W ⊓ V ⟶ W := homOfLE inf_le_left
    -- The section `c • e` over `W ⊓ V` has coordinate `c` and vanishing germ.
    let s := X.presheaf.map j.op c • M.presheaf.map i.op (trivializationGenerator M t)
    have hs : trivializationCoordinate M t i s = X.presheaf.map j.op c := by
      rw [LinearEquiv.map_smul, trivializationCoordinate_map_trivializationGenerator, smul_eq_mul,
        mul_one]
    have h0 : M.presheaf.germ (W ⊓ V) x hxWV s = M.presheaf.germ (W ⊓ V) x hxWV 0 := by
      rw [map_zero, hgerm i, hs, TopCat.Presheaf.germ_res_apply]
      exact hr
    obtain ⟨W', hxW', k, k', hk⟩ := M.presheaf.germ_eq x hxWV hxWV _ _ h0
    rw [map_zero] at hk
    have hc : X.presheaf.map k.op (X.presheaf.map j.op c) = 0 := by
      rw [← hs, ← trivializationCoordinate_map, hk, map_zero]
    rw [← TopCat.Presheaf.germ_res_apply X.presheaf j _ hxWV,
      ← TopCat.Presheaf.germ_res_apply X.presheaf k _ hxW',
      hc, map_zero]
  · exact (Submodule.span_singleton_eq_top_iff _ _).mp (span_germ_trivializationGenerator M x t hxV)

/-- The stalk of an invertible sheaf is a free module over the local ring. -/
instance free_stalk_of_isInvertible :
    Module.Free (X.presheaf.stalk x) (M.presheaf.stalk x) :=
  Module.Free.of_equiv (nonempty_linearEquiv_stalk_of_isInvertible M x).some

/-- The stalk of an invertible sheaf has rank one over the local ring. -/
theorem finrank_stalk_of_isInvertible :
    Module.finrank (X.presheaf.stalk x) (M.presheaf.stalk x) = 1 := by
  rw [← (nonempty_linearEquiv_stalk_of_isInvertible M x).some.finrank_eq, Module.finrank_self]

/-- **A generator of the stalk of an invertible sheaf is a basis.** If the germ `g` generates
the stalk `M_x`, then `a ↦ a • g` is a bijection from the local ring `𝒪_{X,x}` onto `M_x`: since
`M_x` is isomorphic to `𝒪_{X,x}`, a surjective endomorphism of it is injective. -/
theorem bijective_toSpanSingleton_of_span_eq_top {g : M.presheaf.stalk x}
    (hg : Submodule.span (X.presheaf.stalk x) {g} = ⊤) :
    Function.Bijective (LinearMap.toSpanSingleton (X.presheaf.stalk x) _ g) := by
  obtain ⟨e⟩ := nonempty_linearEquiv_stalk_of_isInvertible M x
  have hsurj : Function.Surjective (LinearMap.toSpanSingleton (X.presheaf.stalk x) _ g) :=
    (Submodule.span_singleton_eq_top_iff _ _).mp hg
  have hf := OrzechProperty.bijective_of_surjective_endomorphism
    (e.symm.toLinearMap ∘ₗ LinearMap.toSpanSingleton (X.presheaf.stalk x) _ g)
    (e.symm.surjective.comp hsurj)
  exact ⟨fun a b h ↦ hf.1 (by simp [h]), hsurj⟩

/-- A multiple `a • g` generates the stalk of an invertible sheaf exactly when `a` is a unit of the
local ring and `g` generates the stalk. -/
theorem span_smul_eq_top_iff {a : X.presheaf.stalk x} {g : M.presheaf.stalk x} :
    Submodule.span (X.presheaf.stalk x) {a • g} = ⊤ ↔
      IsUnit a ∧ Submodule.span (X.presheaf.stalk x) {g} = ⊤ := by
  refine ⟨fun h ↦ ?_, fun ⟨ha, hg⟩ ↦ (Submodule.span_singleton_smul_eq ha g).trans hg⟩
  have hg : Submodule.span (X.presheaf.stalk x) {g} = ⊤ :=
    top_le_iff.mp (h ▸ Submodule.span_singleton_smul_le _ a g)
  obtain ⟨b, hb⟩ := (Submodule.span_singleton_eq_top_iff _ _).mp h g
  have hba : b * a = 1 := (bijective_toSpanSingleton_of_span_eq_top M x hg).1 (by simpa [mul_smul])
  exact ⟨.of_mul_eq_one_right _ hba, hg⟩

end AlgebraicGeometry.Scheme.Modules
