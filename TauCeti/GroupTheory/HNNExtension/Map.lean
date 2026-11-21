/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.HNNExtension

/-!
# Homomorphisms of HNN extensions induced by a homomorphism of the base groups

Let `HNNExtension G A B φ` and `HNNExtension H A' B' φ'` be HNN extensions, with stable letters
`t` and `t'`. A homomorphism `f : G →* H` that maps `A` into `A'` compatibly with the associated
isomorphisms, `φ' (f a) = f (φ a)` for `a ∈ A`, induces a homomorphism of HNN extensions that is
`f` on `G` and sends `t` to `t'` (`HNNExtension.map`). This construction is functorial
(`HNNExtension.map_id`, `HNNExtension.map_comp`).

If `f` is injective and pulls `A'` and `B'` back into `A` and `B`, the induced homomorphism is
injective (`HNNExtension.map_injective`): it sends a reduced word `g₀ t^{ε₁} g₁ ⋯ t^{εₙ} gₙ` to
`f g₀ t'^{ε₁} f g₁ ⋯ t'^{εₙ} f gₙ`, which is again reduced, since `f gᵢ` lies in `A'` (or `B'`)
only when `gᵢ` lies in `A` (or `B`). By Britton's lemma a reduced word with a letter `t'` is not
in the base group, so only the words without stable letters can map to `1`. This is the analogue
for HNN extensions of the criterion for subamalgams of amalgamated products
(`Monoid.PushoutI.map_injective`).

## Main definitions

* `HNNExtension.map`: the homomorphism of HNN extensions induced by `f : G →* H`.

## Main results

* `HNNExtension.map_injective`: the injectivity criterion.

## References

* R. C. Lyndon, P. E. Schupp, *Combinatorial group theory*, Springer (1977), Chapter IV, §2
  (Britton's lemma, in Mathlib as `HNNExtension.ReducedWord.toList_eq_nil_of_mem_of_range`).
-/

public section

open Subgroup

namespace HNNExtension

variable {G H : Type*} [Group G] [Group H] {A B : Subgroup G} {φ : A ≃* B} {A' B' : Subgroup H}
  {φ' : A' ≃* B'}

/-- The homomorphism `HNNExtension G A B φ →* HNNExtension H A' B' φ'` that is `f` on `G` and sends
the stable letter to the stable letter, for `f : G →* H` mapping `A` into `A'` compatibly with the
associated isomorphisms: `φ' (f a) = f (φ a)`. -/
def map (f : G →* H) (hA : A ≤ A'.comap f) (hφ : ∀ a : A, (φ' ⟨f a, hA a.property⟩ : H) = f (φ a)) :
    HNNExtension G A B φ →* HNNExtension H A' B' φ' :=
  lift (of.comp f) t fun a ↦ by
    simpa [hφ] using t_mul_of (φ := φ') ⟨f a, hA a.property⟩

variable (f : G →* H) (hA : A ≤ A'.comap f) (hφ : ∀ a : A, (φ' ⟨f a, hA a.property⟩ : H) = f (φ a))

@[simp]
theorem map_of (g : G) : map f hA hφ (of g) = of (f g) :=
  lift_of _ _ _ g

@[simp]
theorem map_t : map f hA hφ t = t :=
  lift_t _ _ _

@[simp]
theorem map_comp_of : (map f hA hφ).comp of = of.comp f :=
  MonoidHom.ext (map_of f hA hφ)

@[simp]
theorem map_id : map (φ := φ) (.id G) (comap_id A).ge (fun _ ↦ rfl) = .id (HNNExtension G A B φ) :=
  hom_ext (by ext; simp) (by simp)

theorem map_comp {K : Type*} [Group K] {A'' B'' : Subgroup K} {φ'' : A'' ≃* B''} (g : H →* K)
    (hA' : A' ≤ A''.comap g) (hφ' : ∀ a : A', (φ'' ⟨g a, hA' a.property⟩ : K) = g (φ' a)) :
    map (g.comp f) (hA.trans <| (comap_mono hA').trans (comap_comap A'' g f).le)
        (fun a ↦ by simpa using (hφ' ⟨f a, hA a.property⟩).trans (congrArg g (hφ a))) =
      (map g hA' hφ').comp (map f hA hφ) :=
  hom_ext (by ext; simp) (by simp)

-- If `f` pulls `A'` and `B'` back into `A` and `B`, then `f g` lies in the associated subgroup
-- `toSubgroup A' B' u` of the target only when `g` lies in `toSubgroup A B u`.
private theorem mem_toSubgroup_of_map {f : G →* H} (hA' : A'.comap f ≤ A) (hB' : B'.comap f ≤ B)
    {u : ℤˣ} {g : G} (hg : f g ∈ toSubgroup A' B' u) : g ∈ toSubgroup A B u := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · exact hA' hg
  · exact hB' hg

-- The image of a reduced word under the homomorphism induced by `f`: `f` applied to every letter
-- of the base group. It is reduced when `f` pulls `A'` and `B'` back into `A` and `B`.
private def mapReducedWord {f : G →* H} (hA' : A'.comap f ≤ A) (hB' : B'.comap f ≤ B)
    (w : NormalWord.ReducedWord G A B) : NormalWord.ReducedWord H A' B' where
  head := f w.head
  toList := w.toList.map fun p ↦ (p.1, f p.2)
  chain := (List.isChain_map _).2 <|
    w.chain.imp fun _ _ h hb ↦ h (mem_toSubgroup_of_map hA' hB' hb)

private theorem prod_mapReducedWord {hA' : A'.comap f ≤ A} {hB' : B'.comap f ≤ B}
    (w : NormalWord.ReducedWord G A B) :
    (mapReducedWord hA' hB' w).prod φ' = map f hA hφ (w.prod φ) := by
  simp [mapReducedWord, NormalWord.ReducedWord.prod, map_list_prod, Function.comp_def]

/-- **Britton transfer.** The homomorphism of HNN extensions induced by an injective `f : G →* H`
that pulls `A'` and `B'` back into `A` and `B` is injective. -/
theorem map_injective {f : G →* H} (hf : Function.Injective f) {hA : A ≤ A'.comap f}
    {hφ : ∀ a : A, (φ' ⟨f a, hA a.property⟩ : H) = f (φ a)} (hA' : A'.comap f ≤ A)
        (hB' : B'.comap f ≤ B) :
    Function.Injective (map f hA hφ) := by
  refine (injective_iff_map_eq_one _).2 fun x hx ↦ ?_
  obtain ⟨d⟩ := NormalWord.TransversalPair.nonempty G A B
  -- Write `x` as a reduced word `w`; its image is a reduced word representing `1`.
  set w := (NormalWord.equiv φ d x).toReducedWord
  have hw : w.prod φ = x := (NormalWord.equiv φ d).symm_apply_apply x
  have hw' : (mapReducedWord hA' hB' w).prod φ' ∈ (of : H →* HNNExtension H A' B' φ').range := by
    rw [prod_mapReducedWord f hA hφ, hw, hx]
    exact one_mem _
  -- By Britton's lemma the image has no stable letters, so neither has `w`.
  have hnil : w.toList = [] :=
    List.map_eq_nil_iff.1 (ReducedWord.toList_eq_nil_of_mem_of_range _ _ hw')
  have hx' : x = of w.head := by simp [← hw, NormalWord.ReducedWord.prod, hnil]
  rw [hx', map_of, map_eq_one_iff _ (of_injective (φ := φ')), map_eq_one_iff _ hf] at hx
  rw [hx', hx, map_one]

end HNNExtension
