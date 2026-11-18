/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.AlgebraicSet
import TauCeti.GroupTheory.PushoutI.Basic

/-!
# The group of a system of equations under an extension of the coefficients

Let `S` be a system of equations over a group `G` in the variables `X`, and `G_S = G[X] ⧸ ncl(S)`
its group. An injective homomorphism `f : G →* H` induces `G[X] →* H[X]`, and the image `f(S)` of
`S` is a system over `H`. If `G` embeds in `G_S`, the induced homomorphism `G_S →* H_{f(S)}` is
injective: `H_{f(S)}` maps to the amalgamated product `H ∗_G G_S`, in which `G_S` embeds, and the
composite `G_S →* H_{f(S)} →* H ∗_G G_S` is that embedding.

## Main results

* `TauCeti.GroupAlgGeom.SystemGroup.comap_normalClosure_image`: if `f` is injective and `G` embeds
  in `G_S`, a word whose image lies in the normal closure of `f(S)` lies in that of `S`.

## References

* [VAR-I] O. Kharlampovich, A. Myasnikov, *Irreducible affine varieties over a free group. I:
  Irreducibility of quadratic equations and Nullstellensatz*, J. Algebra 200 (1998), §1,
  Proposition 2, where this is shown for quadratic equations.
-/

public section

open Function Monoid.Coprod Subgroup

namespace TauCeti.GroupAlgGeom.SystemGroup

variable {G : Type*} [Group G] {X : Type*}

/-- **Change of coefficients.** Let `f : G →* H` be injective and `S` a system of equations over
`G` such that `G` embeds in `G_S`. A word of `G[X]` whose image under `f` lies in the normal
closure of the image of `S` lies in the normal closure of `S`; that is, the homomorphism
`G_S →* H_{f(S)}` induced by `f` is injective. -/
theorem comap_normalClosure_image {H : Type*} [Group H] {f : G →* H} (hf : Injective f)
    {S : Set (GX G X)} (hS : Injective (coeff S)) :
    (normalClosure (Monoid.Coprod.map f (FreeGroup.map id) '' S)).comap
      (Monoid.Coprod.map f (FreeGroup.map id)) = normalClosure S := by
  set F : GX G X →* GX H X := Monoid.Coprod.map f (FreeGroup.map id)
  refine le_antisymm (fun w hw => ?_) (comap_normalClosure_image_ge S F)
  -- `H_{F(S)}` maps to the amalgam `P` of `H` and `G_S` over `G`, in which `G_S` embeds
  obtain ⟨P, _, α, β, -, hβ, hαβ⟩ := Monoid.PushoutI.exists_injective_comp_eq_comp hf hS
  let θ : GX H X →* P :=
    Monoid.Coprod.lift α (FreeGroup.lift fun x => β (inr (FreeGroup.of x) : GX G X))
  have hθ : θ.comp F = β.comp (QuotientGroup.mk' (normalClosure S)) := by
    ext g
    · simpa [θ, F] using DFunLike.congr_fun hαβ g
    · simp [θ, F]
  have hker : normalClosure (F '' S) ≤ θ.ker := by
    refine normalClosure_le_normal ?_
    rintro _ ⟨s, hs, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, ← MonoidHom.comp_apply, hθ]
    simp [(QuotientGroup.eq_one_iff s).2 (subset_normalClosure hs)]
  rw [← QuotientGroup.eq_one_iff, ← map_eq_one_iff β hβ]
  simpa [MonoidHom.mem_ker.1 (hker hw)] using (DFunLike.congr_fun hθ w).symm

end TauCeti.GroupAlgGeom.SystemGroup
