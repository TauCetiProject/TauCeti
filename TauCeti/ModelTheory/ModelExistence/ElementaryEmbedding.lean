/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.ModelExistence.AElementary
public import TauCeti.ModelTheory.Infinitary.FirstOrderImage
public import Mathlib.ModelTheory.ElementaryMaps

/-!
# Elementary embeddings and the first-order image fragment

Fragment elementarity specializes to Mathlib's elementarity on the first-order image
`Fragment.firstOrder L`, the fragment of images of finitary formulas: an embedding is
`Fragment.firstOrder L`-elementary exactly when it preserves and reflects every first-order
formula, which is the condition bundled by Mathlib's `ElementaryEmbedding`. So every elementary
embedding is `A`-elementary for the first-order image, and every embedding that is `A`-elementary
for a fragment `A` containing the first-order image, such as any formation-closed fragment,
bundles as an elementary embedding.

This is how results about `A`-elementary embeddings, such as downward Löwenheim–Skolem for
fragments and the elementarity of directed unions, restrict to first-order logic, and how
Mathlib's elementary embeddings enter arguments phrased with fragments.

## Main results

* `FirstOrder.Language.ElementaryEmbedding.aElementary_firstOrder`: an elementary embedding is
  `A`-elementary for the first-order image.
* `FirstOrder.Language.AElementary.toElementaryEmbedding`: an embedding that is `A`-elementary for
  a fragment containing the first-order image, bundled as an elementary embedding.
* `FirstOrder.Language.aElementary_firstOrder_iff`: an embedding is `A`-elementary for the
  first-order image exactly when it preserves and reflects every first-order formula.

## References

* D. Marker, *Lectures on Infinitary Model Theory*, Cambridge University Press, 2016, Chapter 1.
-/

public section

universe u v w w'

namespace FirstOrder

namespace Language

open BoundedFormula

variable {L : Language.{u, v}} {M : Type w} {N : Type w'} [L.Structure M] [L.Structure N]

/-- An elementary embedding is `A`-elementary for the first-order image fragment. -/
theorem ElementaryEmbedding.aElementary_firstOrder (f : N ↪ₑ[L] M) :
    AElementary (Fragment.firstOrder L) f.toEmbedding := by
  rw [aElementary_iff]
  rintro n _ hφ a
  obtain ⟨φ, rfl⟩ := Fragment.mem_firstOrder_iff.1 hφ
  rw [ElementaryEmbedding.coe_toEmbedding, realize_toInf, realize_toInf,
    ← f.map_boundedFormula φ Empty.elim a]
  -- the empty valuations of the free variables agree
  rw [Subsingleton.elim (f ∘ (Empty.elim : Empty → N)) Empty.elim]

namespace AElementary

variable {A : Fragment L} {f : N ↪[L] M}

/-- An embedding that is `A`-elementary for a fragment `A` containing the first-order image,
bundled as an elementary embedding. Every formation-closed fragment contains the first-order
image, by `Fragment.FormationClosed.firstOrder_le`. -/
def toElementaryEmbedding (h : AElementary A f) (hA : Fragment.firstOrder L ≤ A) :
    N ↪ₑ[L] M where
  toFun := f
  map_formula' n φ x := by
    simpa only [realize_toInf, Formula.realize_relabel_sumInr] using
      (h.mono hA).realize_iff (Fragment.toOmega_mem_firstOrder (relabel Sum.inr φ)) x

/-- The bundled elementary embedding has the same underlying function. -/
@[simp]
theorem coe_toElementaryEmbedding (h : AElementary A f) (hA : Fragment.firstOrder L ≤ A) :
    ⇑(h.toElementaryEmbedding hA) = f :=
  (rfl)

/-- The bundled elementary embedding has the same underlying embedding. -/
@[simp]
theorem toElementaryEmbedding_toEmbedding (h : AElementary A f)
    (hA : Fragment.firstOrder L ≤ A) : (h.toElementaryEmbedding hA).toEmbedding = f :=
  (rfl)

end AElementary

/-- An embedding is `A`-elementary for the first-order image fragment exactly when it preserves
and reflects every first-order formula, the condition defining Mathlib's elementary embeddings. -/
theorem aElementary_firstOrder_iff {f : N ↪[L] M} :
    AElementary (Fragment.firstOrder L) f ↔
      ∀ ⦃n : ℕ⦄ (φ : L.Formula (Fin n)) (x : Fin n → N), φ.Realize (f ∘ x) ↔ φ.Realize x :=
  ⟨fun h _ φ x => (h.toElementaryEmbedding le_rfl).map_formula φ x,
    -- the underlying embedding of `⟨f, h⟩` is `f` by structure eta
    fun h => (ElementaryEmbedding.aElementary_firstOrder ⟨f, h⟩ :)⟩

end Language

end FirstOrder
