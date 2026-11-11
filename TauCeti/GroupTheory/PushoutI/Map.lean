/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.PushoutI
import TauCeti.GroupTheory.CoprodI.Word
import TauCeti.GroupTheory.PushoutI.Reduced

/-!
# Homomorphisms of amalgamated products induced by homomorphisms of the factors

Let `φ i : H →* G i` and `φ' i : H' →* G' i` be two families of homomorphisms over the same index
type, with amalgamated products `Monoid.PushoutI φ` and `Monoid.PushoutI φ'`. Homomorphisms
`f i : G i →* G' i` and `k : H →* H'` with `f i ∘ φ i = φ' i ∘ k` induce a homomorphism
`Monoid.PushoutI.map f k _ : Monoid.PushoutI φ →* Monoid.PushoutI φ'`.

For groups, with the `φ' i` and `k` injective, the induced homomorphism is injective as soon as
every `f i` pulls the amalgamated subgroup `φ' i H'` back into `φ i H`
(`Monoid.PushoutI.map_injective`). This is the usual criterion for a subamalgam, a consequence of
the normal form theorem. The `f i` and the `φ i` need not be assumed injective: under these
hypotheses they are.

## Main definitions

* `Monoid.PushoutI.map`: the homomorphism of amalgamated products induced by a compatible family
  of homomorphisms of the factors and of the amalgamated monoids.

## Main results

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

/-- A homomorphism of amalgamated products of groups induced by homomorphisms `f i` of the factors
and an injective homomorphism `k` of the amalgamated groups is injective if the structure maps of
the target are injective and each `f i` pulls the amalgamated subgroup of the target back into the
amalgamated subgroup of the source. -/
theorem map_injective {f : ∀ i, G i →* G' i} {k : H →* H'}
    (hfk : ∀ i, (f i).comp (φ i) = (φ' i).comp k) (hφ' : ∀ i, Injective (φ' i)) (hk : Injective k)
    (hf : ∀ i g, f i g ∈ (φ' i).range → g ∈ (φ i).range) : Injective (map f k hfk) := by
  have hφk (i : ι) : Injective (f i ∘ φ i) := by
    rw [← MonoidHom.coe_comp, hfk]
    exact (hφ' i).comp hk
  have hf1 (i : ι) (g : G i) (hg : f i g = 1) : g = 1 := by
    obtain ⟨h, rfl⟩ := hf i g (hg ▸ one_mem _)
    rw [hφk i (a₁ := h) (a₂ := 1) (by simpa using hg), map_one]
  refine (injective_iff_map_eq_one _).2 fun x hx => ?_
  obtain ⟨h, w, hw, rfl⟩ := exists_eq_base_mul_ofCoprodI_prod x
  have hw' : Reduced φ' (w.map f hf1) := fun l hl => by
    rw [Word.toList_map] at hl
    obtain ⟨l₀, hl₀, rfl⟩ := List.mem_map.1 hl
    exact fun hmem => hw l₀ hl₀ (hf _ _ hmem)
  have hempty : w = .empty := by
    have h' := hw'.eq_empty_of_mem_range hφ' ⟨k h⁻¹, by
      rwa [map_inv, map_inv, eq_comm, ← mul_eq_one_iff_eq_inv', Word.prod_map,
        ← map_ofCoprodI f k hfk, ← map_base f k hfk, ← map_mul]⟩
    ext1
    simpa using congrArg Word.toList h'
  subst hempty
  simp only [Word.prod_empty, map_one, mul_one, map_base] at hx ⊢
  rw [(map_eq_one_iff _ hk).1 ((map_eq_one_iff _ (base_injective hφ')).1 hx), map_one]

end Group

end Monoid.PushoutI
