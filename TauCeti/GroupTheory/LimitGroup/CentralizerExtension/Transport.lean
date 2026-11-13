/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.LimitGroup.CentralizerExtension.Iterated
public import TauCeti.GroupTheory.LimitGroup.CentralizerExtension.Map

/-!
# Iterated extensions of centralizers along an embedding of the base

A chain of admissible extensions of centralizers over `G` can be transported along an embedding
`f : G →* E` of `G` in a fully residually free group `E`: the top `K` of the chain embeds in the
top of a chain over `E`, compatibly with the coefficient homomorphisms.

The steps of the chain are transported one at a time. If `g : K →* E'` embeds the top of a chain
over `G` in the top of a chain over `E`, the homomorphism `K(u, ℤⁿ) →* E'(g u, ℤⁿ)` induced by `g`
is injective (`TauCeti.LimitGroup.CentralizerExt.map_injective`). The parameter `g u` may be a
proper power in `E'`; since `E'` is again fully residually free, `g u` has a root `r` that is not
a proper power with the same centralizer, and `E'(g u, ℤⁿ)` is the admissible extension
`E'(r, ℤⁿ)` (`TauCeti.LimitGroup.CentralizerExt.congr`).

Transport composes embeddings in ICE groups: if `K` embeds over `F` in the top `E` of a chain over
`F`, a chain over `K` is transported along `K ↪ E` and appended to the chain over `F`. This is the
identification `G(U₀, T₀)(U₂, T₂) = G(U₀ ∪ U₂, T₀ ∪ T₂)` at the end of the proof of
Theorem 4 of Kharlampovich–Myasnikov's *Irreducible affine varieties over a free group. I*.

## Main results

* `TauCeti.LimitGroup.ICE.exists_embedding_of_injective`: transport of a chain of extensions of
  centralizers along an embedding of the base in a fully residually free group.
* `TauCeti.LimitGroup.ICE.exists_embedding_comp`: over a fully residually free `F`, if `K` embeds
  in an ICE group over `F` and `L` embeds in an ICE group over `K`, then `L` embeds in an ICE group
  over `F`, compatibly with the coefficients.

## References

* O. Kharlampovich, A. Myasnikov, *Irreducible affine varieties over a free group. I:
  Irreducibility of quadratic equations and Nullstellensatz*, J. Algebra 200 (1998), §0, and §6,
  proof of Theorem 4.
* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), §2.5.
-/

public section

universe u v

namespace TauCeti.LimitGroup

namespace ICE

variable {G K : Type u} {E : Type v} [Group G] [Group K] [Group E]

/-- **Transport of an iterated extension of centralizers along an embedding of the base.** If `G`
embeds in a fully residually free group `E` by `f`, then every ICE group `K` over `G` embeds in an
ICE group `E'` over `E`, by an embedding `g` restricting to `f` on the coefficients:
`g ∘ j = j' ∘ f`, where `j : G →* K` and `j' : E →* E'` are the coefficient inclusions.

If `E` is itself an ICE group over some `F`, appending the new chain (`ICE.append`) gives a chain
over `F` whose top contains `K`. -/
theorem exists_embedding_of_injective (hE : IsFullyResiduallyFree E) {f : G →* E}
    (hf : Function.Injective f) {j : G →* K} (d : ICE G K j) :
    ∃ (E' : Type v) (_ : Group E') (j' : E →* E') (_ : ICE E E' j') (g : K →* E'),
      Function.Injective g ∧ g.comp j = j'.comp f := by
  induction d with
  | refl => exact ⟨E, _, .id E, refl, f, hf, by simp⟩
  | @step K _ j _ u n h ih =>
    obtain ⟨E', _, j', c, g, hg, hgj⟩ := ih
    -- `E'` is fully residually free, so `g u ≠ 1` is a power of some `r` that is not a proper
    -- power, with the same centralizer.
    obtain ⟨r, -, -, -, hr, hC⟩ :=
      (c.isFullyResiduallyFree hE).isResiduallyFree.centralizerExt_root_reduction
        ((map_ne_one_iff g hg).2 h.ne_one)
    -- Embed `K(u, ℤⁿ)` in `E'(g u, ℤⁿ)`, which is the admissible extension `E'(r, ℤⁿ)`.
    refine ⟨CentralizerExt r n, _, CentralizerExt.of.comp j',
      c.step (isAdmissibleCentralizerStep_iff.2 ⟨hr, h.pos⟩),
      (CentralizerExt.congr hC).toMonoidHom.comp (CentralizerExt.map g u n),
      (CentralizerExt.congr hC).injective.comp (CentralizerExt.map_injective hg u n), ?_⟩
    ext x
    simpa using DFunLike.congr_fun hgj x

/-- **Composition of embeddings in iterated extensions of centralizers.** Let `F` be fully
residually free. If `K` embeds over `F` in an ICE group `E` over `F` (by `f` with `f ∘ κ = j`), and
`L` embeds over `K` in an ICE group `E'` over `K` (by `g` with `g ∘ l = j'`), then there are an ICE
group `E''` over `F`, with coefficient inclusion `j''`, and an embedding `h` of `L` in `E''` with
`h ∘ l ∘ κ = j''`.

The group `K` itself need not be an ICE group over `F`, and `κ`, `l` need not be the coefficient
inclusions of chains. -/
theorem exists_embedding_comp {F E : Type u} {K E' : Type v} {L : Type*} [Group F] [Group K]
    [Group L] [Group E] [Group E'] (hF : IsFullyResiduallyFree F) {κ : F →* K} {l : K →* L}
    {j : F →* E} (c : ICE F E j) (f : GroupAlgGeom.GHom κ j) (hf : Function.Injective f)
    {j' : K →* E'} (c' : ICE K E' j') (g : GroupAlgGeom.GHom l j') (hg : Function.Injective g) :
    ∃ (E'' : Type u) (_ : Group E'') (j'' : F →* E'') (_ : ICE F E'' j'')
      (h : GroupAlgGeom.GHom (l.comp κ) j''), Function.Injective h := by
  -- `E` is fully residually free, so the chain `c'` over `K` can be transported along `f`.
  obtain ⟨E'', _, j'', d, g', hg', hgj⟩ :=
    exists_embedding_of_injective (c.isFullyResiduallyFree hF) (f := f) hf c'
  exact ⟨E'', _, j''.comp j, c.append d,
    ⟨g'.comp g, fun x => by simpa using DFunLike.congr_fun hgj (κ x)⟩, hg'.comp hg⟩

end ICE

/-! ### Over the free group of rank two -/

/-- `ICE.exists_embedding_comp` with both chains nonempty and a non-surjective middle embedding:
over `F = F(a, b)`, with `K = F` embedded in `E = F(a, ℤ)` and `L = F(b, ℤ)` an ICE group over `K`,
it gives an embedding of `F(b, ℤ)` over `F` in an ICE group over `F`. -/
example : ∃ (E : Type) (_ : Group E) (j : FreeGroup (Fin 2) →* E) (_ : ICE (FreeGroup (Fin 2)) E j)
    (h : GroupAlgGeom.GHom ((CentralizerExt.of : FreeGroup (Fin 2) →*
      CentralizerExt (FreeGroup.of (1 : Fin 2)) 1).comp (.id _)) j), Function.Injective h :=
  ICE.exists_embedding_comp isFullyResiduallyFree_of_isFreeGroup
    (.single (isAdmissibleCentralizerStep_freeGroup_of (0 : Fin 2) one_pos))
    ⟨CentralizerExt.of, fun _ => rfl⟩ CentralizerExt.of_injective
    (.single (isAdmissibleCentralizerStep_freeGroup_of (1 : Fin 2) one_pos))
    (.id _) (by simpa using Function.injective_id)

end TauCeti.LimitGroup
