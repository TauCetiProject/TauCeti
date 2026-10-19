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
-/

public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

universe u

variable {X : Scheme.{u}} (M : X.Modules)
  [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X M] (x : X)

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
  · intro m
    obtain ⟨W, hxW, s, rfl⟩ := M.presheaf.exists_germ_eq m
    have hxWV : x ∈ W ⊓ V := Opens.mem_inf.mpr ⟨hxW, hxV⟩
    let i : W ⊓ V ⟶ V := homOfLE inf_le_right
    let j : W ⊓ V ⟶ W := homOfLE inf_le_left
    refine ⟨X.presheaf.germ (W ⊓ V) x hxWV
      (trivializationCoordinate M t i (M.presheaf.map j.op s)), ?_⟩
    rw [LinearMap.toSpanSingleton_apply, ← hgerm, TopCat.Presheaf.germ_res_apply]

/-- The stalk of an invertible sheaf is a free module over the local ring. -/
instance free_stalk_of_isInvertible :
    Module.Free (X.presheaf.stalk x) (M.presheaf.stalk x) :=
  Module.Free.of_equiv (nonempty_linearEquiv_stalk_of_isInvertible M x).some

/-- The stalk of an invertible sheaf has rank one over the local ring. -/
theorem finrank_stalk_of_isInvertible :
    Module.finrank (X.presheaf.stalk x) (M.presheaf.stalk x) = 1 := by
  rw [← (nonempty_linearEquiv_stalk_of_isInvertible M x).some.finrank_eq, Module.finrank_self]

end AlgebraicGeometry.Scheme.Modules
