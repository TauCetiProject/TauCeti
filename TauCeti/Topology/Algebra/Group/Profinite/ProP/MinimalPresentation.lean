/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Free.Rank
public import TauCeti.Topology.Algebra.Group.Profinite.Presentation.Basic

/-!
# Minimal presentations of pro-`p` groups

A continuous surjection `f : G ↠ H` of pro-`p` groups, with `G` topologically finitely generated,
preserves the topological generator rank exactly when `ker f ≤ Φ(G)`
(`TauCeti.IsProP.topologicalGeneratorRankNat_eq_iff_ker_le_proPFrattini`). Applied to the
quotient map from a free pro-`p` group of finite rank onto a presented pro-`p` group, whose kernel
is the closed normal closure of the relators (`TauCeti.presentedProP.ker_mk`), this characterizes
**minimal presentations**: a presentation `G ≅ ⟨X ∣ rels⟩` with `X` finite is minimal, meaning
`Nat.card X = d(G)`, exactly when every relator lies in the Frattini subgroup
`Φ(F) = closure (Fᵖ [F, F])` of the free pro-`p` group `F` on `X`. Every topologically finitely
generated pro-`p` group has such a presentation, on any finite type of cardinality `d(G)`. This is
the condition `R ≤ Φ(F)` on the relation subgroup under which the relation rank of `G` is read off
from the presentation, and it is the normalization a Demushkin relator satisfies.

Minimal presentations of a group on a given finite type are unique up to a change of basis of the
free group. Two continuous surjections `g, h : F ↠ H` from the free pro-`p` group of finite rank,
with `ker g ≤ Φ(F)`, satisfy `h = g ∘ α` for a continuous automorphism `α` of `F`. Consequently two
pro-`p` groups presented on the same finite type, the second presentation minimal, are
topologically isomorphic exactly when an automorphism of the free group carries the relation
subgroup of the first onto that of the second. This is the form in which an isomorphism of
one-relator groups becomes a statement about the relators, as in Labute's classification of
Demushkin groups.

## Main results

* `TauCeti.presentedProP.topologicalGeneratorRankNat_le_card`: a pro-`p` group presented on a
  finite type `X` has rank at most `Nat.card X`.
* `TauCeti.presentedProP.topologicalGeneratorRankNat_eq_card_iff`: a pro-`p` group presented on a
  finite type `X` has rank `Nat.card X` exactly when the relators lie in the Frattini subgroup of
  the free pro-`p` group on `X`.
* `TauCeti.presentedProP.subset_proPFrattini_iff_card_eq`: a presentation of `G` on a finite type
  `X` has its relators in the Frattini subgroup exactly when `Nat.card X = d(G)`.
* `TauCeti.presentedProP.linearIndependent_frattiniQuotient_of`: the classes of the generators of a
  minimal presentation are linearly independent in the Frattini quotient.
* `TauCeti.presentedProP.topologicalClosure_normalClosure_eq_proPFrattini`: the relation subgroup
  of a minimal presentation of a group with trivial pro-`p` Frattini subgroup is `Φ(F)`.
* `TauCeti.IsProP.exists_subset_proPFrattini_continuousMulEquiv_presentedProP`: every
  topologically finitely generated pro-`p` group has a minimal presentation on any finite type of
  cardinality `d(G)`.
* `TauCeti.freeProP.exists_continuousMulEquiv_comp_eq`: two continuous surjections of a free
  pro-`p` group of finite rank onto the same Hausdorff group, one of them with kernel in the
  Frattini subgroup, differ by a continuous automorphism of the free group.
* `TauCeti.presentedProP.exists_continuousMulEquiv_topologicalClosure_normalClosure_image_eq`: an
  isomorphism of presented pro-`p` groups with minimal target lifts to an automorphism of the free
  group carrying one relation subgroup onto the other.
* `TauCeti.presentedProP.nonempty_continuousMulEquiv_iff`: two pro-`p` groups presented on the same
  finite type, the second minimally, are isomorphic exactly when their relation subgroups are
  related by an automorphism of the free group.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Section 2.8 and Section 7.8.
* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, Section III.9.
* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), Sections 1
  and 3.
-/

public section

namespace TauCeti

universe u v

variable {p : ℕ} [Fact p.Prime]

namespace presentedProP

variable {X : Type u} [Finite X] (rels : Set (freeProP p X))

/-- A pro-`p` group presented on a finite type `X` has topological generator rank at most
`Nat.card X`: it is the image of the free pro-`p` group on `X`, of rank `Nat.card X`, under the
continuous surjection `mk`. -/
theorem topologicalGeneratorRankNat_le_card :
    topologicalGeneratorRankNat (presentedProP p X rels) isTopologicallyFinitelyGenerated ≤
      Nat.card X := by
  rw [← topologicalGeneratorRankNat_freeProP p (isTopologicallyFinitelyGenerated_freeProP p X)]
  exact topologicalGeneratorRankNat_le_of_surjective (mk p rels : freeProP p X →* _)
    (map_continuous (mk p rels)) (mk_surjective p rels) _

/-- **Minimal presentations.** A pro-`p` group presented on a finite type `X` has topological
generator rank `Nat.card X` exactly when every relator lies in the Frattini subgroup of the free
pro-`p` group on `X`. -/
theorem topologicalGeneratorRankNat_eq_card_iff :
    topologicalGeneratorRankNat (presentedProP p X rels) isTopologicallyFinitelyGenerated =
        Nat.card X ↔
      rels ⊆ proPFrattini p (freeProP p X) := by
  rw [← topologicalGeneratorRankNat_freeProP p (isTopologicallyFinitelyGenerated_freeProP p X),
    (isProP_freeProP p X).topologicalGeneratorRankNat_eq_iff_ker_le_proPFrattini
      (isTopologicallyFinitelyGenerated_freeProP p X) (mk p rels : freeProP p X →* _)
      (map_continuous (mk p rels)) (mk_surjective p rels),
    ker_mk, Subgroup.topologicalClosure_normalClosure_le_iff isClosed_proPFrattini]

omit [Finite X] in
/-- **The generators of a minimal presentation are linearly independent in the Frattini
quotient.** If every relator lies in the Frattini subgroup of the free pro-`p` group on `X`, the
classes of the canonical generators of `⟨X ∣ rels⟩` in its Frattini quotient are linearly
independent over `𝔽_p`, for a generating type `X` of any cardinality: the relation subgroup lies in
the Frattini subgroup, so `mk` induces an injection of Frattini quotients. -/
theorem linearIndependent_frattiniQuotient_of (hrels : rels ⊆ proPFrattini p (freeProP p X)) :
    LinearIndependent (ZMod p) fun x : X ↦
      Additive.ofMul
        (QuotientGroup.mk' (proPFrattini p (presentedProP p X rels)) (of p rels x)) := by
  have hker : (mk p rels : freeProP p X →* presentedProP p X rels).ker ≤
      proPFrattini p (freeProP p X) := by
    rw [ker_mk, Subgroup.topologicalClosure_normalClosure_le_iff isClosed_proPFrattini]
    exact hrels
  have hle : proPFrattini p (freeProP p X) ≤
      (proPFrattini p (presentedProP p X rels)).comap (mk p rels : freeProP p X →* _) :=
    (mk p rels : freeProP p X →* presentedProP p X rels).proPFrattini_le_comap
      (map_continuous (mk p rels)) (mk_surjective p rels)
  -- The map of Frattini quotients induced by `mk` is injective, because the kernel of `mk` lies
  -- in the Frattini subgroup.
  have hinj : Function.Injective (QuotientGroup.map _ _ _ hle) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_map,
      comap_proPFrattini_eq_of_surjective Fact.out
        (mk p rels : freeProP p X →* presentedProP p X rels) (map_continuous (mk p rels))
        (mk_surjective p rels),
      sup_eq_left.2 hker, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  let φ : Additive (freeProP p X ⧸ proPFrattini p (freeProP p X)) →ₗ[ZMod p]
      Additive (presentedProP p X rels ⧸ proPFrattini p (presentedProP p X rels)) :=
    (MonoidHom.toAdditive (QuotientGroup.map _ _ _ hle)).toZModLinearMap p
  have hφ : LinearMap.ker φ = ⊥ := LinearMap.ker_eq_bot.2 fun a b hab ↦
    Additive.toMul.injective (hinj (Additive.ofMul.injective hab))
  convert (freeProP.linearIndependent_frattiniQuotient_of p X).map' φ hφ using 1
  funext x
  simp [φ, mk_of]

variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- A presentation `G ≅ ⟨X ∣ rels⟩` of a topologically finitely generated group on a finite type
`X` has all its relators in the Frattini subgroup of the free pro-`p` group on `X` exactly when it
is minimal, that is when `Nat.card X` is the topological generator rank of `G`. -/
theorem subset_proPFrattini_iff_card_eq (e : presentedProP p X rels ≃ₜ* G)
    (h : IsTopologicallyFinitelyGenerated G) :
    rels ⊆ proPFrattini p (freeProP p X) ↔ Nat.card X = topologicalGeneratorRankNat G h := by
  rw [← topologicalGeneratorRankNat_eq_card_iff, topologicalGeneratorRankNat_congr e, eq_comm]

omit [Finite X] [Fact p.Prime] [IsTopologicalGroup G] in
variable {rels} in
/-- **The relation subgroup of a minimal presentation of a group with trivial Frattini subgroup
is the Frattini subgroup of the free group.** For a presentation `G ≅ ⟨X ∣ rels⟩` with relators in
`Φ(F)`, `F` the free pro-`p` group on `X`, of a topological group `G` with `Φ(G) = 1`, the closed
normal closure of the relators is `Φ(F)`. -/
theorem topologicalClosure_normalClosure_eq_proPFrattini
    (hrels : rels ⊆ proPFrattini p (freeProP p X)) (e : presentedProP p X rels ≃ₜ* G)
    (hΦ : proPFrattini p G = ⊥) :
    (Subgroup.normalClosure rels).topologicalClosure = proPFrattini p (freeProP p X) := by
  refine le_antisymm
    ((Subgroup.topologicalClosure_normalClosure_le_iff isClosed_proPFrattini).mpr hrels)
    fun x hx ↦ ?_
  -- `Φ(F)` maps into `Φ(G) = 1`, so it dies in `⟨X ∣ rels⟩`, hence lies in the relation subgroup.
  have hmem := (mk p rels : _ →* presentedProP p X rels).map_proPFrattini_le
    (map_continuous (mk p rels)) (mk_surjective p rels) ⟨x, hx, rfl⟩
  have hmem' := Subgroup.mem_map_of_mem e.toMulEquiv.toMonoidHom hmem
  rw [e.map_proPFrattini_eq, hΦ, Subgroup.mem_bot] at hmem'
  exact (mk_eq_one_iff x).mp (e.injective (by simpa using hmem'))

end presentedProP

namespace freeProP

variable {X : Type u} [Finite X] {H : Type v} [Group H] [TopologicalSpace H] [T2Space H]

/-- **Two surjections of a free pro-`p` group onto the same group differ by an automorphism when
one of them is minimal.** Let `F` be the free pro-`p` group on a finite type and let `g, h : F → H`
be continuous surjections onto a Hausdorff group, the kernel of `g` lying in the Frattini subgroup
`Φ(F)`. Then `h = g ∘ α` for a continuous automorphism `α` of `F`. -/
theorem exists_continuousMulEquiv_comp_eq (g h : freeProP p X →ₜ* H) (hg : Function.Surjective g)
    (hker : (g : freeProP p X →* H).ker ≤ proPFrattini p (freeProP p X))
    (hh : Function.Surjective h) :
    ∃ α : freeProP p X ≃ₜ* freeProP p X, g.comp (α : freeProP p X →ₜ* freeProP p X) = h := by
  choose y hy using fun x : X ↦ hg (h (of x))
  set β := lift (isProP_freeProP p X) y
  have hβ : g.comp β = h := hom_ext fun x ↦ by simp [β, hy]
  have hsurj : Function.Surjective β :=
    (isProP_freeProP p X).surjective_of_surjective_comp_of_ker_le_proPFrattini
      (s := (β : freeProP p X →* freeProP p X)) (isCompact_range β.continuous).isClosed
      (by simpa [← ContinuousMonoidHom.coe_comp, hβ] using hh) hker
  refine ⟨(isTopologicallyFinitelyGenerated_freeProP p X).continuousMulEquivOfSurjective
    β.continuous hsurj, ContinuousMonoidHom.ext fun x ↦ ?_⟩
  simpa using DFunLike.congr_fun hβ x

end freeProP

namespace presentedProP

variable {X : Type u} {rels rels' : Set (freeProP p X)}

omit [Fact p.Prime] in
private theorem map_topologicalClosure_normalClosure (α : freeProP p X ≃ₜ* freeProP p X)
    (s : Set (freeProP p X)) :
    (Subgroup.normalClosure s).topologicalClosure.map α.toMulEquiv.toMonoidHom =
      (Subgroup.normalClosure (α '' s)).topologicalClosure := by
  calc
    _ = ((Subgroup.normalClosure s).map
        α.toMulEquiv.toMonoidHom).topologicalClosure := by
      apply SetLike.coe_injective
      rw [Subgroup.coe_map, Subgroup.topologicalClosure_coe, Subgroup.topologicalClosure_coe,
        Subgroup.coe_map]
      exact α.toHomeomorph.image_closure _
    _ = _ := by
      rw [Subgroup.map_normalClosure s α.toMulEquiv.toMonoidHom α.surjective]
      congr 2

/-- **Isomorphic presentations with a minimal target differ by a change of basis.** Let
`⟨X ∣ rels⟩` and `⟨X ∣ rels'⟩` be pro-`p` groups presented on the same finite type, with the
relators `rels'` in the Frattini subgroup of the free pro-`p` group `F` on `X`. Every topological
isomorphism `e` between them lifts to a continuous automorphism `α` of `F`, and `α` carries the
relation subgroup of the first presentation onto that of the second: the closed normal closure of
the relators `α '' rels` is the closed normal closure of `rels'`. For one relator on each side this
reads `closure ⟪α r⟫ = closure ⟪r'⟫`, since `α '' {r} = {α r}`. -/
theorem exists_continuousMulEquiv_topologicalClosure_normalClosure_image_eq [Finite X]
    (hrels' : rels' ⊆ proPFrattini p (freeProP p X))
    (e : presentedProP p X rels ≃ₜ* presentedProP p X rels') :
    ∃ α : freeProP p X ≃ₜ* freeProP p X, (∀ x, mk p rels' (α x) = e (mk p rels x)) ∧
      (Subgroup.normalClosure (α '' rels)).topologicalClosure =
        (Subgroup.normalClosure rels').topologicalClosure := by
  have hker : (mk p rels' : freeProP p X →* presentedProP p X rels').ker ≤
      proPFrattini p (freeProP p X) := by
    rw [ker_mk, Subgroup.topologicalClosure_normalClosure_le_iff isClosed_proPFrattini]
    exact hrels'
  obtain ⟨α, hα⟩ := freeProP.exists_continuousMulEquiv_comp_eq (mk p rels')
    ((e : presentedProP p X rels →ₜ* presentedProP p X rels').comp (mk p rels))
    (mk_surjective p rels') hker (e.surjective.comp (mk_surjective p rels))
  have hαx (x : freeProP p X) : mk p rels' (α x) = e (mk p rels x) := by
    simpa using DFunLike.congr_fun hα x
  refine ⟨α, hαx, le_antisymm ?_ fun x hx ↦ ?_⟩
  · -- `α` sends every relator of `rels` into the kernel of `mk p rels'`.
    rw [Subgroup.topologicalClosure_normalClosure_le_iff (Subgroup.isClosed_topologicalClosure _)]
    rintro _ ⟨r, hr, rfl⟩
    rw [SetLike.mem_coe, ← mk_eq_one_iff, hαx, mk_relator r hr, map_one]
  · -- Conversely `α⁻¹ x` dies in `⟨X ∣ rels⟩`.
    have hsymm : α.symm x ∈ (Subgroup.normalClosure rels).topologicalClosure := by
      rw [← mk_eq_one_iff, ← map_eq_one_iff e e.injective, ← hαx, α.apply_symm_apply,
        mk_eq_one_iff]
      exact hx
    rw [← map_topologicalClosure_normalClosure α rels, Subgroup.mem_map_equiv]
    exact hsymm

/-- **Presentations of isomorphic groups, one of them minimal, differ by a change of basis.**
Pro-`p` groups presented on the same finite type `X`, with the relators `rels'` in the Frattini
subgroup of the free pro-`p` group `F` on `X`, are topologically isomorphic exactly when a
continuous automorphism `α` of `F` carries the closed normal closure of `rels` onto that of
`rels'`, that is when the closed normal closure of `α '' rels` is the closed normal closure of
`rels'`. -/
theorem nonempty_continuousMulEquiv_iff [Finite X]
    (hrels' : rels' ⊆ proPFrattini p (freeProP p X)) :
    Nonempty (presentedProP p X rels ≃ₜ* presentedProP p X rels') ↔
      ∃ α : freeProP p X ≃ₜ* freeProP p X,
        (Subgroup.normalClosure (α '' rels)).topologicalClosure =
          (Subgroup.normalClosure rels').topologicalClosure := by
  refine ⟨fun ⟨e⟩ ↦ ?_, fun ⟨α, hα⟩ ↦ ⟨congr α (fun r hr ↦ ?_) fun r hr ↦ ?_⟩⟩
  · obtain ⟨α, -, hα⟩ :=
      exists_continuousMulEquiv_topologicalClosure_normalClosure_image_eq hrels' e
    exact ⟨α, hα⟩
  · rw [mk_eq_one_iff, ← hα]
    exact Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure ⟨r, hr, rfl⟩)
  · -- Apply `α⁻¹` to the transported relation subgroup.
    rw [mk_eq_one_iff]
    have hr' : r ∈ (Subgroup.normalClosure (α '' rels)).topologicalClosure :=
      hα ▸ Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure hr)
    rw [← map_topologicalClosure_normalClosure α rels, Subgroup.mem_map_equiv] at hr'
    exact hr'

end presentedProP

/-- **Existence of minimal presentations.** A topologically finitely generated pro-`p` group has a
presentation on any finite type of cardinality its topological generator rank, with all relators in
the Frattini subgroup of the free pro-`p` group. -/
theorem IsProP.exists_subset_proPFrattini_continuousMulEquiv_presentedProP {G : Type u} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
    (hG : IsProP p G) (h : IsTopologicallyFinitelyGenerated G) (X : Type u) [Finite X]
    (hX : Nat.card X = topologicalGeneratorRankNat G h) :
    ∃ rels : Set (freeProP p X), rels ⊆ proPFrattini p (freeProP p X) ∧
      Nonempty (presentedProP p X rels ≃ₜ* G) := by
  obtain ⟨rels, ⟨e⟩⟩ := hG.exists_continuousMulEquiv_presentedProP h X hX.ge
  exact ⟨rels, (presentedProP.subset_proPFrattini_iff_card_eq rels e h).mpr hX, ⟨e⟩⟩

end TauCeti
