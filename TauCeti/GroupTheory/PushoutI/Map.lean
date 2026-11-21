/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.PushoutI
public import Mathlib.Order.Filter.Defs
import Mathlib.Order.Filter.Finite
import Mathlib.Order.Filter.Map
import TauCeti.GroupTheory.CoprodI.Word
import TauCeti.GroupTheory.PushoutI.Reduced

/-!
# Homomorphisms of amalgamated products induced by homomorphisms of the factors

Let `φ i : H →* G i` and `φ' i : H' →* G' i` be two families of homomorphisms over the same index
type, with amalgamated products `Monoid.PushoutI φ` and `Monoid.PushoutI φ'`. Homomorphisms
`f i : G i →* G' i` and `k : H →* H'` with `f i ∘ φ i = φ' i ∘ k` induce a homomorphism
`Monoid.PushoutI.map f k _ : Monoid.PushoutI φ →* Monoid.PushoutI φ'`.

For groups, the normal form theorem gives a criterion for the induced homomorphisms to keep
nonidentity elements, in an eventual form for a family of homomorphisms `map (f a) (k a) _` indexed
by `a : α` along a filter (`Monoid.PushoutI.eventually_map_ne_one`): if the structure maps
`φ' a i` of the targets are eventually injective, the `k a` eventually keep every nonidentity
element of `H` and every letter of a factor outside the amalgamated subgroup is eventually mapped
by the `f a i` outside the amalgamated subgroup of the target, then the reduced words of
`PushoutI φ` are eventually mapped to reduced words, so every nonidentity element is eventually
kept. For a single homomorphism this is the usual injectivity criterion for a subamalgam
(`Monoid.PushoutI.map_injective`): the `φ' i` and `k` injective and every `f i` pulling the
amalgamated subgroup `φ' i H'` back into `φ i H`. The `f i` and the `φ i` need not be assumed
injective: under these hypotheses they are.

## Main definitions

* `Monoid.PushoutI.map`: the homomorphism of amalgamated products induced by a compatible family
  of homomorphisms of the factors and of the amalgamated monoids.

## Main results

* `Monoid.PushoutI.eventually_map_ne_one`: the eventual criterion for a family of induced
  homomorphisms to keep every nonidentity element.
* `Monoid.PushoutI.map_injective`: the injectivity criterion.

## References

* J.-P. Serre, *Trees*, Chapter I, §1.2, Theorem 1 (the normal form theorem for amalgamated
  products, in Mathlib as `Monoid.PushoutI.Reduced.eq_empty_of_mem_range`).
-/

public section

namespace Monoid.PushoutI

open Function CoprodI

variable {ι : Type*} {G G' : ι → Type*} {H H' : Type*}

section Monoid

variable [∀ i, Monoid (G i)] [∀ i, Monoid (G' i)] [Monoid H] [Monoid H'] {φ : ∀ i, H →* G i}
  {φ' : ∀ i, H' →* G' i}

/-- The homomorphism `PushoutI φ →* PushoutI φ'` of amalgamated products induced by homomorphisms
`f i : G i →* G' i` of the factors and `k : H →* H'` of the amalgamated monoids that are
compatible with the structure maps: `f i ∘ φ i = φ' i ∘ k`. -/
def map (f : ∀ i, G i →* G' i) (k : H →* H') (hfk : ∀ i, (f i).comp (φ i) = (φ' i).comp k) :
    PushoutI φ →* PushoutI φ' :=
  lift (fun i => (of i).comp (f i)) ((base φ').comp k) fun i => by
    rw [MonoidHom.comp_assoc, hfk, ← MonoidHom.comp_assoc, of_comp_eq_base]

variable (f : ∀ i, G i →* G' i) (k : H →* H') (hfk : ∀ i, (f i).comp (φ i) = (φ' i).comp k)

@[simp]
theorem map_of (i : ι) (g : G i) : map f k hfk (of i g) = of i (f i g) := by
  simp [map]

@[simp]
theorem map_base (h : H) : map f k hfk (base φ h) = base φ' (k h) := by
  simp [map]

@[simp]
theorem map_comp_of (i : ι) : (map f k hfk).comp (of i) = (of i).comp (f i) :=
  MonoidHom.ext (map_of f k hfk i)

@[simp]
theorem map_comp_base : (map f k hfk).comp (base φ) = (base φ').comp k :=
  MonoidHom.ext (map_base f k hfk)

/-- On the free product of the factors, the induced homomorphism is the homomorphism of free
products induced by the `f i`. -/
@[simp]
theorem map_comp_ofCoprodI :
    (map f k hfk).comp ofCoprodI = ofCoprodI.comp (CoprodI.lift fun i => CoprodI.of.comp (f i)) :=
  CoprodI.ext_hom _ _ fun i => by ext; simp

@[simp]
theorem map_ofCoprodI (x : CoprodI G) :
    map f k hfk (ofCoprodI x) = ofCoprodI (CoprodI.lift (fun i => CoprodI.of.comp (f i)) x) :=
  DFunLike.congr_fun (map_comp_ofCoprodI f k hfk) x

@[simp]
theorem map_id : map (φ := φ) (fun i => .id (G i)) (.id H) (fun _ => rfl) = .id (PushoutI φ) :=
  hom_ext (by simp) (by ext; simp)

theorem map_comp {G'' : ι → Type*} {H'' : Type*} [∀ i, Monoid (G'' i)] [Monoid H'']
    {φ'' : ∀ i, H'' →* G'' i} (f' : ∀ i, G' i →* G'' i) (k' : H' →* H'')
    (hfk' : ∀ i, (f' i).comp (φ' i) = (φ'' i).comp k') :
    map (fun i => (f' i).comp (f i)) (k'.comp k) (fun i => by
      rw [MonoidHom.comp_assoc, hfk, ← MonoidHom.comp_assoc, hfk', MonoidHom.comp_assoc]) =
      (map f' k' hfk').comp (map f k hfk) :=
  hom_ext (fun i => by ext; simp) (by ext; simp)

end Monoid

section Group

variable [∀ i, Group (G i)] [∀ i, Group (G' i)] [Group H] [Group H'] {φ : ∀ i, H →* G i}
  {φ' : ∀ i, H' →* G' i}

/-- **Normal form criterion, eventual form.** Let
`map (f a) (k a) _ : PushoutI φ →* PushoutI (φ' a)` be homomorphisms of amalgamated products of
groups indexed by `a : α`. If along a filter on `α` the structure maps `φ' a i` are eventually
injective, the `k a` eventually keep every nonidentity element of `H`, and every element of a factor
outside the amalgamated subgroup is eventually mapped by the `f a i` outside the amalgamated
subgroup of the target, then the induced homomorphisms eventually keep every nonidentity
element. -/
theorem eventually_map_ne_one {α : Type*} {l : Filter α} {G' : α → ι → Type*} {H' : α → Type*}
    [∀ a i, Group (G' a i)] [∀ a, Group (H' a)] {φ' : ∀ a i, H' a →* G' a i}
    {f : ∀ a i, G i →* G' a i} {k : ∀ a, H →* H' a}
    (hfk : ∀ a i, (f a i).comp (φ i) = (φ' a i).comp (k a))
    (hφ' : ∀ᶠ a in l, ∀ i, Injective (φ' a i))
    (hk : ∀ h : H, h ≠ 1 → ∀ᶠ a in l, k a h ≠ 1)
    (hf : ∀ i (g : G i), g ∉ (φ i).range → ∀ᶠ a in l, f a i g ∉ (φ' a i).range)
    {x : PushoutI φ} (hx : x ≠ 1) : ∀ᶠ a in l, map (f a) (k a) (hfk a) x ≠ 1 := by
  -- Write `x = h * a₁ * ⋯ * aᵣ` with `h ∈ H` and a reduced word `a₁ ⋯ aᵣ`.
  obtain ⟨h, w, hw, rfl⟩ := exists_eq_base_mul_ofCoprodI_prod x
  rcases eq_or_ne w .empty with rfl | hne
  · -- A word with no letters: `x = h ≠ 1`, and its image `k a h` is eventually nontrivial.
    have hh : h ≠ 1 := by
      rintro rfl
      simp at hx
    filter_upwards [hk h hh, hφ'] with a ha hφa
    simpa [map_eq_one_iff _ (base_injective hφa)] using ha
  -- Otherwise the images of the letters eventually stay outside the amalgamated subgroup, so the
  -- image of the word is reduced and nonempty, and its product is not in the amalgamated subgroup.
  filter_upwards [(Filter.eventually_all_finite w.toList.finite_toSet).2 fun y hy =>
    hf _ _ (hw y hy), hφ'] with a ha hφa h1
  have hfw : ∀ y ∈ w.toList, f a y.1 y.2 ≠ 1 := fun y hy h1 => ha y hy (h1 ▸ one_mem _)
  have hw' : Reduced (φ' a) (w.map (f a) hfw) := fun y hy => by
    rw [Word.toList_map] at hy
    obtain ⟨y₀, hy₀, rfl⟩ := List.mem_map.1 hy
    exact ha y₀ hy₀
  -- The image of `x` is `k a h` times the product of the image word, so that product is
  -- `(k a h)⁻¹`, in the amalgamated subgroup.
  rw [map_mul, map_base, map_ofCoprodI, ← Word.prod_map _ hfw] at h1
  refine hne <| (Word.map_eq_empty_iff _ hfw).1 <|
    hw'.eq_empty_of_mem_range hφa ⟨k a h⁻¹, ?_⟩
  rw [map_inv, map_inv]
  exact (eq_inv_of_mul_eq_one_right h1).symm

/-- A homomorphism of amalgamated products of groups induced by homomorphisms `f i` of the factors
and an injective homomorphism `k` of the amalgamated groups is injective if the structure maps of
the target are injective and each `f i` pulls the amalgamated subgroup of the target back into the
amalgamated subgroup of the source. -/
theorem map_injective {f : ∀ i, G i →* G' i} {k : H →* H'}
    (hfk : ∀ i, (f i).comp (φ i) = (φ' i).comp k) (hφ' : ∀ i, Injective (φ' i)) (hk : Injective k)
    (hf : ∀ i g, f i g ∈ (φ' i).range → g ∈ (φ i).range) : Injective (map f k hfk) :=
  (injective_iff_map_eq_one _).2 fun _ hx => by_contra fun hne => Filter.eventually_pure.1
    (eventually_map_ne_one (l := pure ()) (G' := fun _ => G') (H' := fun _ => H')
      (φ' := fun _ => φ') (f := fun _ => f) (k := fun _ => k) (fun _ => hfk)
      (.of_forall fun _ => hφ')
      (fun _ hh => Filter.eventually_pure.2 ((map_ne_one_iff k hk).2 hh))
      (fun i g hg => Filter.eventually_pure.2 (mt (hf i g) hg)) hne) hx

end Group

end Monoid.PushoutI
