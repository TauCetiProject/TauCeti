/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Pi.Basic
public import Mathlib.CategoryTheory.EssentialImage
public import Mathlib.CategoryTheory.Functor.FullyFaithful

/-!
# Products of functors

For families of functors `G i : A i ⥤ B i`, the product functor `Functor.pi G` is fully faithful
when every `G i` is (`CategoryTheory.Functor.FullyFaithful.pi`), and essentially surjective when
every `G i` is (`CategoryTheory.Functor.essSurj_pi`).
-/

@[expose] public section

namespace CategoryTheory

variable {I : Type*} {A B : I → Type*} [∀ i, Category (A i)] [∀ i, Category (B i)]

/-- The product of fully faithful functors is fully faithful. -/
def Functor.FullyFaithful.pi {G : ∀ i, A i ⥤ B i} (hG : ∀ i, (G i).FullyFaithful) :
    (Functor.pi G).FullyFaithful where
  preimage φ i := (hG i).preimage (φ i)
  map_preimage φ := funext fun i ↦ (hG i).map_preimage (φ i)
  preimage_map φ := funext fun i ↦ (hG i).preimage_map (φ i)

/-- The product of essentially surjective functors is essentially surjective. -/
instance Functor.essSurj_pi (G : ∀ i, A i ⥤ B i) [∀ i, (G i).EssSurj] :
    (Functor.pi G).EssSurj where
  mem_essImage Y :=
    ⟨fun i ↦ (G i).objPreimage (Y i), ⟨Pi.isoMk fun i ↦ (G i).objObjPreimageIso (Y i)⟩⟩

end CategoryTheory
