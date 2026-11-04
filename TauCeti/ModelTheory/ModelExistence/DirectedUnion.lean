/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.ModelExistence.AElementary
public import Mathlib.ModelTheory.Substructures
import TauCeti.ModelTheory.Substructures

/-!
# Directed unions of fragment-elementary substructures and omitting types

Let `A` be a fragment of `L_{ω₁ω}` and `S` a nonempty directed family of substructures of one
structure `M`, each `A`-elementary in `M`. Then their union is `A`-elementary in `M`, and each
member is `A`-elementary in the union; in particular this applies to chains indexed by a nonempty
directed order, such as `ℕ` or `ω₁`. No countability of the family or of the language and no
formation closure of `A` is needed. A partial type whose members lie in `A` and that each member
omits is omitted by the union.

## Main results

* `FirstOrder.Language.aElementary_iSup`: the union of a nonempty directed family of
  `A`-elementary substructures is `A`-elementary.
* `FirstOrder.Language.aElementary_inclusion_iSup`: each member is `A`-elementary in the union.
* `FirstOrder.Language.aElementary_iSup_of_monotone`: the chain form.
* `FirstOrder.Language.OmitsType.iSup`: omission of a partial type in `A` passes to directed
  unions.

## References

* D. Marker, *Lectures on Infinitary Model Theory*, Cambridge University Press, 2016, Chapter 1.
* Ported from `cameronfreer/infinitary-logic` at commit
  `518a366cba97b1ae8c4dc64a297a396939bc3e0b`, `InfinitaryLogic/ModelTheory/AElementaryChains.lean`.
* Divergences from that source: the type-omission predicate is named `OmitsType` rather than
  `OmitsFiniteType`, and its passage to substructures is stated for arbitrary
  `A`-elementary embeddings, beside `AElementary`; the step that places a tuple of the union in one
  member is `Substructure.exists_forall_mem_of_directed`; the chain form assumes a directed order
  rather than a linear order.
-/

public section

universe u v w

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} {M : Type w} [L.Structure M] {A : Fragment L}
  {ι : Type*} [Nonempty ι] {S : ι → L.Substructure M}

/-- **Directed unions.** The union of a nonempty directed family of `A`-elementary substructures
is `A`-elementary. -/
theorem aElementary_iSup (hdir : Directed (· ≤ ·) S) (hS : ∀ i, AElementary A (S i).subtype) :
    AElementary A (⨆ i, S i).subtype := by
  refine aElementary_of_tarskiVaught _ fun φ hφ a ⟨m, hm⟩ => ?_
  -- the tuple lies in one member `S k`, written `b`
  obtain ⟨k, hk⟩ := Substructure.exists_forall_mem_of_directed hdir a
  let b : Fin _ → S k := fun i => ⟨a i, hk i⟩
  have hab : (⨆ i, S i).subtype ∘ a = (S k).subtype ∘ b := rfl
  -- `∀ x, φ` fails at `b` in `M`, hence in `S k`, which supplies a counterexample
  have hfail : ¬ (BoundedFormulaInf.all φ).Realize Empty.elim b := by
    rw [← (hS k).realize_iff hφ b, ← hab, BoundedFormulaInf.realize_all]
    exact fun h => hm (h m)
  rw [BoundedFormulaInf.realize_all] at hfail
  push Not at hfail
  obtain ⟨c, hc⟩ := hfail
  refine ⟨⟨c, Substructure.mem_iSup_of_directed hdir |>.2 ⟨k, c.2⟩⟩, fun h => hc ?_⟩
  rw [← (hS k).realize_iff (A.all_mem hφ), Fin.comp_snoc, ← hab]
  exact h

/-- **Each member is `A`-elementary in the union.** -/
theorem aElementary_inclusion_iSup (hdir : Directed (· ≤ ·) S)
    (hS : ∀ i, AElementary A (S i).subtype) (i : ι) :
    AElementary A (Substructure.inclusion (le_iSup S i)) :=
  (aElementary_iSup hdir hS).of_comp
    ((Substructure.subtype_comp_inclusion (le_iSup S i)).symm ▸ hS i)

/-- **Chains.** The union of a monotone family of `A`-elementary substructures indexed by a
nonempty directed order is `A`-elementary. -/
theorem aElementary_iSup_of_monotone [Preorder ι] [IsDirectedOrder ι] (hmono : Monotone S)
    (hS : ∀ i, AElementary A (S i).subtype) : AElementary A (⨆ i, S i).subtype :=
  aElementary_iSup hmono.directed_le hS

/-! ### Omitting types -/

/-- **Omission passes to directed unions.** If each member of a nonempty directed family of
`A`-elementary substructures omits a partial type whose members lie in `A`, so does the union. -/
theorem OmitsType.iSup (hdir : Directed (· ≤ ·) S) (hS : ∀ i, AElementary A (S i).subtype)
    {n : ℕ} {p : Set (L.BoundedFormulaω Empty n)}
    (hp : ∀ φ ∈ p, (⟨n, φ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A)
    (h : ∀ i, OmitsType (S i) p) : OmitsType (⨆ i, S i : L.Substructure M) p := by
  refine omitsType_iff.2 fun a => ?_
  obtain ⟨k, hk⟩ := Substructure.exists_forall_mem_of_directed hdir a
  obtain ⟨φ, hφp, hφ⟩ := omitsType_iff.1 (h k) fun i => ⟨a i, hk i⟩
  refine ⟨φ, hφp, fun hr => hφ ?_⟩
  -- the member `S k` is `A`-elementary in the union, which reflects the realization
  exact ((aElementary_inclusion_iSup hdir hS k).realize_iff (hp φ hφp) _).1 hr

end Language

end FirstOrder
