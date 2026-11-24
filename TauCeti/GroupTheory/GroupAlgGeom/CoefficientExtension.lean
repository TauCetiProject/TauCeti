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
its group. A homomorphism `f : G →* H` induces `G[X] →* H[X]`, and the image `f(S)` of `S` is a
system over `H`. For a system `T` over `H` such that `f(S)` is a consequence of `T`, this induces
`G_S →* H_T`. If `f` is injective, `G` embeds in `G_S` and `T` is in turn a consequence of `f(S)`,
the induced homomorphism is injective: `H_{f(S)}` maps to the amalgamated product `H ∗_G G_S`, in
which `G_S` embeds, and the composite `G_S →* H_{f(S)} →* H ∗_G G_S` is that embedding.

## Main definitions

* `TauCeti.GroupAlgGeom.SystemGroup.map`: the homomorphism `G_S →* H_T` induced by `f : G →* H`.
  It is functorial: the identity of `G` induces the identity (`map_id`), and `g ∘ f` induces the
  composite of the homomorphisms induced by `f` and `g` (`map_comp_map`, `map_map`).

## Main results

* `TauCeti.GroupAlgGeom.SystemGroup.comap_normalClosure_image`: if `f` is injective and `G` embeds
  in `G_S`, a word whose image lies in the normal closure of `f(S)` lies in that of `S`.
* `TauCeti.GroupAlgGeom.SystemGroup.map_injective`: if moreover `T` and `f(S)` are consequences of
  each other, the homomorphism `G_S →* H_T` induced by `f` is injective.

## References

* [VAR-I] O. Kharlampovich, A. Myasnikov, *Irreducible affine varieties over a free group. I:
  Irreducibility of quadratic equations and Nullstellensatz*, J. Algebra 200 (1998), §1,
  Proposition 2, where this is shown for quadratic equations.
-/

public section

open Function Monoid.Coprod Subgroup

namespace TauCeti.GroupAlgGeom.SystemGroup

variable {G H X : Type*} [Group G] [Group H] {S : Set (GX G X)} {T : Set (GX H X)}

/-- The homomorphism `G_S →* H_T` induced by `f : G →* H`, for systems `S` over `G` and `T` over
`H` such that the image under `f` of each equation of `S` is a consequence of `T`. -/
def map (f : G →* H) (h : Monoid.Coprod.map f (FreeGroup.map id) '' S ⊆ normalClosure T) :
    SystemGroup G S →* SystemGroup H T :=
  QuotientGroup.map _ _ (Monoid.Coprod.map f (FreeGroup.map id))
    (normalClosure_le_normal (Set.image_subset_iff.1 h))

/-- The homomorphism `G_S →* H_T` induced by `f` sends the class of a word `w` to the class of its
image, in which each coefficient `g` is replaced by `f g` and the variables are unchanged. -/
@[simp]
theorem map_mk (f : G →* H) (h : Monoid.Coprod.map f (FreeGroup.map id) '' S ⊆ normalClosure T)
    (w : GX G X) :
    map f h (w : SystemGroup G S) = (Monoid.Coprod.map f (FreeGroup.map id) w : SystemGroup H T) :=
  (rfl)

/-- The homomorphism `G_S →* H_T` induced by `f` is compatible with the coefficients: it sends
`g ∈ G` to `f g`. -/
theorem map_comp_coeff (f : G →* H)
    (h : Monoid.Coprod.map f (FreeGroup.map id) '' S ⊆ normalClosure T) :
    (map f h).comp (coeff S) = (coeff T).comp f := by
  ext
  simp

/-- Changing the coefficients along the identity of `G` induces the identity of `G_S`. -/
@[simp]
theorem map_id (h : Monoid.Coprod.map (.id G) (FreeGroup.map id) '' S ⊆ normalClosure S) :
    map (.id G) h = .id (SystemGroup G S) := by
  ext <;> simp

/-- If `f(S)` is a consequence of `T` and `g(T)` is a consequence of `U`, then `(g ∘ f)(S)` is a
consequence of `U`. -/
theorem image_comp_subset_normalClosure {K : Type*} [Group K] {U : Set (GX K X)} {f : G →* H}
    {g : H →* K} (hf : Monoid.Coprod.map f (FreeGroup.map id) '' S ⊆ normalClosure T)
    (hg : Monoid.Coprod.map g (FreeGroup.map id) '' T ⊆ normalClosure U) :
    Monoid.Coprod.map (g.comp f) (FreeGroup.map id) '' S ⊆ normalClosure U := by
  rintro _ ⟨s, hs, rfl⟩
  simpa [Monoid.Coprod.map_map, FreeGroup.map_eq_lift, FreeGroup.lift_of_eq_id] using
    congrArg (map g hg) ((QuotientGroup.eq_one_iff _).2 (hf ⟨s, hs, rfl⟩))

/-- Changing the coefficients along `f` and then along `g` induces the same homomorphism
`G_S →* K_U` as changing them along `g ∘ f`. -/
@[simp]
theorem map_comp_map {K : Type*} [Group K] {U : Set (GX K X)} (f : G →* H) (g : H →* K)
    (hf : Monoid.Coprod.map f (FreeGroup.map id) '' S ⊆ normalClosure T)
    (hg : Monoid.Coprod.map g (FreeGroup.map id) '' T ⊆ normalClosure U) :
    (map g hg).comp (map f hf) = map (g.comp f) (image_comp_subset_normalClosure hf hg) := by
  ext <;> simp

/-- Changing the coefficients along `f` and then along `g` is changing them along `g ∘ f`. -/
@[simp]
theorem map_map {K : Type*} [Group K] {U : Set (GX K X)} (f : G →* H) (g : H →* K)
    (hf : Monoid.Coprod.map f (FreeGroup.map id) '' S ⊆ normalClosure T)
    (hg : Monoid.Coprod.map g (FreeGroup.map id) '' T ⊆ normalClosure U) (x : SystemGroup G S) :
    map g hg (map f hf x) = map (g.comp f) (image_comp_subset_normalClosure hf hg) x :=
  DFunLike.congr_fun (map_comp_map f g hf hg) x

/-- **Change of coefficients.** Let `f : G →* H` be injective and `S` a system of equations over
`G` such that `G` embeds in `G_S`. A word of `G[X]` whose image under `f` lies in the normal
closure of the image of `S` lies in the normal closure of `S`; that is, the homomorphism
`G_S →* H_{f(S)}` induced by `f` is injective. -/
theorem comap_normalClosure_image {f : G →* H} (hf : Injective f) (hS : Injective (coeff S)) :
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

/-- **Change of coefficients for system groups.** Let `f : G →* H` be injective, `S` a system over
`G` such that `G` embeds in `G_S`, and `T` a system over `H` such that `f(S)` and `T` are
consequences of each other. Then the homomorphism `G_S →* H_T` induced by `f` is injective. -/
theorem map_injective {f : G →* H} (hf : Injective f) (hS : Injective (coeff S))
    (h : Monoid.Coprod.map f (FreeGroup.map id) '' S ⊆ normalClosure T)
    (hT : T ⊆ normalClosure (Monoid.Coprod.map f (FreeGroup.map id) '' S)) :
    Injective (map f h) :=
  (QuotientGroup.map_injective_iff _ _ _ _).2 <| (comap_normalClosure_image hf hS).le.trans' <|
    comap_mono (normalClosure_le_normal hT)

end TauCeti.GroupAlgGeom.SystemGroup
