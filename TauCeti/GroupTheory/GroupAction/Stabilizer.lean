/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import TauCeti.Algebra.GroupAction.OrbitRelQuotient
import TauCeti.Algebra.Group.Subgroup.Pointwise
import TauCeti.GroupTheory.QuotientGroup.Basic

/-!
# Point stabilisers: their cardinality, and when they are normal

A count defined through a point stabiliser is useful only alongside the rules for moving it.
Three such rules are recorded here, all consequences of Mathlib machinery rather than new
mathematics, and all stated for `Nat.card` because that is the form a numerical invariant of
an orbit is wanted in. The first of them is what lets the count descend to the orbit space, so
that descent is recorded here as well, as the definition `cardStabilizerOnOrbit`.

*Along an orbit* the stabiliser order does not change: related points have conjugate
stabilisers, by `MulAction.stabilizerEquivStabilizerOfOrbitRel`.

*Along an equivariant injection* it does not change either: a map `α → β` carrying the action of
`G` to that of `H` along a group isomorphism `G ≃* H`, and separating the point from its
translates, identifies the stabilisers. So when the map is an equivalence, the equivalence of
orbit spaces it induces, `TauCeti.MulAction.orbitRelQuotientCongr`, preserves
`cardStabilizerOnOrbit`, and so does the splitting `TauCeti.MulAction.orbitRelQuotientSumEquiv` of
the orbit space of an action on a sum `α ⊕ β`. These are what move a weighted count of orbits from
one action to another.

*Along a surjection* it divides: if `f : G →* H` is onto and the two actions agree at the point
in question, then the `G`-order of that point's stabiliser is `Nat.card f.ker` times its
`H`-order. Taking `f` to be a quotient map gives the projective case, where the divisor is the
subgroup quotiented out.

A point stabiliser of a permutation representation `ρ : G →* Equiv.Perm α` is a subgroup of the
source, namely the comap of the stabiliser in `Equiv.Perm α`. The last two results say when that
subgroup is the kernel — so in particular normal — and, for a transitive representation, that
normality of it is equivalent to freeness of the action of the image.

## Main results

* `TauCeti.card_stabilizer_of_orbitRel`: the stabiliser order is an invariant of the orbit,
  with `TauCeti.card_stabilizer_smul` the translate-presented corollary.
* `TauCeti.cardStabilizerOnOrbit`: that order as a function on the orbit space, with
  `TauCeti.cardStabilizerOnOrbit_mk` its evaluation lemma.
* `TauCeti.card_stabilizer_congr`: the stabiliser order is preserved by a map carrying one action
  to another along a group isomorphism, if it separates the point from its translates.
* `TauCeti.cardStabilizerOnOrbit_orbitRelQuotientCongr`: the orbit-space equivalence
  `TauCeti.MulAction.orbitRelQuotientCongr` induced by an equivariant equivalence preserves the
  stabiliser orders.
* `TauCeti.cardStabilizerOnOrbit_orbitRelQuotientSumEquiv_symm`: the splitting
  `TauCeti.MulAction.orbitRelQuotientSumEquiv` of the orbit space of an action on `α ⊕ β`
  preserves the stabiliser orders.
* `TauCeti.card_stabilizer_eq_card_ker_mul_card_stabilizer`: the stabiliser order divides by
  `Nat.card f.ker` along a surjection `f`, with
  `TauCeti.card_stabilizer_eq_card_subgroup_mul_card_stabilizer_quotient` the quotient-map
  corollary and
  `TauCeti.card_stabilizer_eq_card_subgroupOf_mul_card_stabilizer_map` its relative form, for a
  subgroup mapped into the quotient.
* `TauCeti.card_stabilizer_subgroupOf`: the degenerate case of that surjection, where the map is
  the isomorphism `𝒢.subgroupOf ℋ ≃* 𝒢` and the order is unchanged.
* `TauCeti.card_stabilizer_coset_eq_card_stabilizer_inv_smul`: the class of `g` in `G ⧸ H` has,
  inside `stabilizer G p`, a stabiliser of the same order as `g⁻¹ • p` has inside `H` —
  conjugation by `g` is the bijection.
* `MonoidHom.comap_stabilizer_eq_ker`: the point stabiliser of a permutation representation is
  its kernel as soon as the image has trivial stabiliser at that point, and
  `MonoidHom.normal_comap_stabilizer_iff_isCancelSMul`: for a transitive representation that
  happens exactly when the image acts freely, which is exactly when the point stabiliser is
  normal.
-/

public section

namespace TauCeti

variable {G α : Type*} [Group G] [MulAction G α]

/-- **The order of a stabiliser is constant along an orbit**: points related by the orbit
relation have conjugate stabilisers, hence stabilisers of equal cardinality.

This is what lets a count defined through a point stabiliser — the order `e_P` of an elliptic
point of a Fuchsian group, say — be read as an invariant of the orbit. It holds with no
finiteness hypothesis: for an infinite stabiliser both sides are `0`, by `Nat.card`'s
convention. -/
theorem card_stabilizer_of_orbitRel {a b : α} (h : MulAction.orbitRel G α a b) :
    Nat.card (MulAction.stabilizer G a) = Nat.card (MulAction.stabilizer G b) :=
  Nat.card_congr (MulAction.stabilizerEquivStabilizerOfOrbitRel h).toEquiv

/-- The orbit invariance of `card_stabilizer_of_orbitRel` in the form wanted when the second
point is presented as a translate of the first.

Not `@[simp]`: whether `Nat.card (MulAction.stabilizer G (g • a))` is in normal form depends on
the action, since a `simp` lemma for the particular `•` can rewrite inside it. -/
theorem card_stabilizer_smul (g : G) (a : α) :
    Nat.card (MulAction.stabilizer G (g • a)) = Nat.card (MulAction.stabilizer G a) :=
  card_stabilizer_of_orbitRel (MulAction.orbitRel_apply.mpr (MulAction.mem_orbit a g))

/-- **The stabiliser order as a function on the orbit space.** `card_stabilizer_of_orbitRel`
says the order is constant along an orbit, so it descends to `MulAction.orbitRel.Quotient G α`,
which is the form wanted when the count is summed over orbits rather than over points.

Note this counts the stabiliser in `G` itself. When the action is not faithful the kernel sits
inside every stabiliser and inflates each value by `Nat.card` of it — so for a group acting
through a quotient, this is the order upstairs, not the order of the group that acts
effectively. `card_stabilizer_eq_card_subgroup_mul_card_stabilizer_quotient` is the conversion
between the two. -/
noncomputable def cardStabilizerOnOrbit (q : MulAction.orbitRel.Quotient G α) : ℕ :=
  Quotient.liftOn' q (fun a ↦ Nat.card (MulAction.stabilizer G a))
    fun _ _ h ↦ card_stabilizer_of_orbitRel h

/-- Evaluating `cardStabilizerOnOrbit` on the orbit of `a` recovers the stabiliser order at
`a`. -/
@[simp]
theorem cardStabilizerOnOrbit_mk (a : α) :
    cardStabilizerOnOrbit (Quotient.mk'' a : MulAction.orbitRel.Quotient G α) =
      Nat.card (MulAction.stabilizer G a) := by
  unfold cardStabilizerOnOrbit
  rfl

section Congr

variable {H β : Type*} [Group H] [MulAction H β]

/-- **Stabiliser orders are preserved by an equivariant injection**: if `f : α → β` carries the
`G`-action at `a` to the `H`-action along a group isomorphism `φ : G ≃* H`, and separates `a`
from its translates, then `φ` maps the stabiliser of `a` onto that of `f a`, so the two have the
same order.

Both hypotheses are asked for only at `a`, as that is all the count needs: a caller holding an
equivariant injective `f` supplies `fun g ↦ hφ g a` and `fun _ h ↦ hf h`. -/
theorem card_stabilizer_congr (φ : G ≃* H) {f : α → β} (a : α)
    (hφ : ∀ g : G, f (g • a) = φ g • f a) (hf : ∀ g : G, f (g • a) = f a → g • a = a) :
    Nat.card (MulAction.stabilizer H (f a)) = Nat.card (MulAction.stabilizer G a) :=
  Nat.card_congr (φ.toEquiv.subtypeEquiv fun g ↦ by
    simpa [← hφ] using ⟨congrArg f, hf g⟩).symm

/-- `MulAction.orbitRelQuotientCongr` preserves the stabiliser order of an orbit. -/
@[simp]
theorem cardStabilizerOnOrbit_orbitRelQuotientCongr (φ : G ≃* H) (e : α ≃ β)
    (he : ∀ (g : G) (a : α), e (g • a) = φ g • e a) (q : MulAction.orbitRel.Quotient G α) :
    cardStabilizerOnOrbit (MulAction.orbitRelQuotientCongr φ e he q) = cardStabilizerOnOrbit q :=
  Quotient.inductionOn' q fun a ↦ by simpa only [MulAction.orbitRelQuotientCongr_mk,
    cardStabilizerOnOrbit_mk] using card_stabilizer_congr φ a (he · a) fun _ h ↦ e.injective h

end Congr

section Sum

variable {β : Type*} [MulAction G β]

/-- `MulAction.orbitRelQuotientSumEquiv` preserves the stabiliser order of an orbit: the orbit it
sends to `Sum.inl q` or to `Sum.inr q` has the stabiliser order of `q`. -/
@[simp]
theorem cardStabilizerOnOrbit_orbitRelQuotientSumEquiv_symm
    (s : MulAction.orbitRel.Quotient G α ⊕ MulAction.orbitRel.Quotient G β) :
    cardStabilizerOnOrbit (MulAction.orbitRelQuotientSumEquiv.symm s) =
      s.elim cardStabilizerOnOrbit cardStabilizerOnOrbit := by
  rcases s with (q | q) <;> induction q using Quotient.inductionOn' <;>
    simp only [MulAction.orbitRelQuotientSumEquiv_symm_inl_mk,
      MulAction.orbitRelQuotientSumEquiv_symm_inr_mk, cardStabilizerOnOrbit_mk, Sum.elim_inl,
      Sum.elim_inr] <;>
    exact card_stabilizer_congr (.refl G) _ (by simp) (by simp)

end Sum

/-- **A surjection of acting groups divides stabiliser orders by its kernel**: if `f : G →* H`
is surjective and the `H`-action agrees with the `G`-action along `f` *at the point `a`*, then
the stabiliser of `a` in `G` is `Nat.card f.ker` times its stabiliser in `H`.

Compatibility is asked for only at `a`, not globally, since that is all the count needs; a
caller holding the global statement supplies `fun g ↦ h g a`. -/
theorem card_stabilizer_eq_card_ker_mul_card_stabilizer {H : Type*} [Group H] [MulAction H α]
    (f : G →* H) (hf : Function.Surjective f) (a : α) (hcompat : ∀ g : G, f g • a = g • a) :
    Nat.card (MulAction.stabilizer G a) =
      Nat.card f.ker * Nat.card (MulAction.stabilizer H a) := by
  -- `QuotientGroup.preimageMkEquivSubgroupProdSet` would shorten this, but it is stated only
  -- for `QuotientGroup.mk`; at this generality the kernel-and-Lagrange chain is the route, and
  -- the whole of it rests on this one transport, used in both directions.
  have hmem : ∀ g : G, g ∈ MulAction.stabilizer G a ↔ f g ∈ MulAction.stabilizer H a :=
    fun g ↦ by simp [MulAction.mem_stabilizer_iff, hcompat g]
  have hle : f.ker ≤ MulAction.stabilizer G a := fun n hn ↦
    (hmem n).mpr (by simp [MonoidHom.mem_ker.mp hn])
  let φ : MulAction.stabilizer G a →* MulAction.stabilizer H a :=
    (f.comp (MulAction.stabilizer G a).subtype).codRestrict _ fun g ↦ (hmem _).mp g.2
  have hsurj : Function.Surjective φ := fun ⟨q, hq⟩ ↦ by
    obtain ⟨g, rfl⟩ := hf q
    -- `rfl` here is the `codRestrict`/`Subtype.val` unfolding of `φ`
    exact ⟨⟨g, (hmem g).mpr hq⟩, rfl⟩
  have hker : φ.ker = f.ker.subgroupOf (MulAction.stabilizer G a) :=
    MonoidHom.ker_codRestrict _ _ _
  rw [← φ.ker.card_mul_index, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj, hker,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]
  simp

/-- **Passing to a quotient group divides stabiliser orders by the subgroup**: the case of
`card_stabilizer_eq_card_ker_mul_card_stabilizer` for the quotient map, whose kernel is `N`.

This is the step from a matrix-group stabiliser order to the projective one. The divisor is
`Nat.card N` in general; for `SL(2, ℤ) ↠ PSL(2, ℤ)` that is the centre `±1`, so there the
elliptic orders `e_P` are the matrix counts halved. For a Fuchsian `Γ` with `-I ∉ Γ` the two
counts coincide. -/
theorem card_stabilizer_eq_card_subgroup_mul_card_stabilizer_quotient (N : Subgroup G) [N.Normal]
    [MulAction (G ⧸ N) α] (a : α)
    (hcompat : ∀ g : G, (QuotientGroup.mk g : G ⧸ N) • a = g • a) :
    Nat.card (MulAction.stabilizer G a) =
      Nat.card N * Nat.card (MulAction.stabilizer (G ⧸ N) a) := by
  have h := card_stabilizer_eq_card_ker_mul_card_stabilizer (QuotientGroup.mk' N)
    (QuotientGroup.mk'_surjective N) a hcompat
  rwa [QuotientGroup.ker_mk'] at h

/-- **The relative form: a subgroup, and its image in the quotient.** For `Γ ≤ G`, the stabiliser
of `a` in `Γ` is `Nat.card (N.subgroupOf Γ)` — the part of `N` that `Γ` actually contains — times
the stabiliser of `a` in the image of `Γ` in `G ⧸ N`.

`card_stabilizer_eq_card_subgroup_mul_card_stabilizer_quotient` is the case `Γ = ⊤`, where the
divisor is all of `N`. The relative statement is what a Fuchsian group needs, where `Γ` is a
subgroup of `SL(2, ℤ)` and `N` the centre: there the divisor measures how much of `±I` lies in
`Γ`, and the projective elliptic order `e_P` is the matrix stabiliser order divided by it.
Evaluating that divisor is a fact about the particular `Γ` and is not proved here. -/
theorem card_stabilizer_eq_card_subgroupOf_mul_card_stabilizer_map (N : Subgroup G) [N.Normal]
    [MulAction (G ⧸ N) α] (Γ : Subgroup G) (a : α)
    (hcompat : ∀ g : Γ, (QuotientGroup.mk (g : G) : G ⧸ N) • a = (g : G) • a) :
    Nat.card (MulAction.stabilizer Γ a) = Nat.card (N.subgroupOf Γ) *
      Nat.card (MulAction.stabilizer (Γ.map (QuotientGroup.mk' N)) a) := by
  rw [card_stabilizer_eq_card_ker_mul_card_stabilizer ((QuotientGroup.mk' N).subgroupMap Γ)
    (MonoidHom.subgroupMap_surjective _ _) a hcompat, Subgroup.ker_subgroupMap,
    QuotientGroup.ker_mk']

/-- **Stabiliser orders agree across `subgroupOf`.** For `𝒢 ≤ ℋ`, a point has the same stabiliser
order in `𝒢.subgroupOf ℋ` as in `𝒢` itself.

This is the transport wanted whenever an orbit count produced inside `ℋ` has to be read against
the `𝒢`-orbit it weights, since `cardStabilizerOnOrbit` reads the order in `𝒢`. Mathlib's
`stabilizerEquivStabilizer` transports between two *points* of one group, not between two groups
at one point, so it does not apply here. -/
-- Not `@[simp]`, tested: the same reason as `card_stabilizer_smul` above — the left-hand side is
-- not in simp-normal form, because `MulAction.mem_stabilizer_iff` rewrites the membership
-- condition underneath the `Nat.card`, taking it to `Nat.card { x // x • a = a }`. `simpNF`
-- rejects the attribute.
theorem card_stabilizer_subgroupOf {𝒢 ℋ : Subgroup G} (hle : 𝒢 ≤ ℋ) (a : α) :
    Nat.card (MulAction.stabilizer (↥(𝒢.subgroupOf ℋ)) a) =
      Nat.card (MulAction.stabilizer 𝒢 a) := by
  -- the degenerate case of `card_stabilizer_eq_card_ker_mul_card_stabilizer`: the two groups act
  -- through the same elements of `G`, so the comparison map `Subgroup.subgroupOfEquivOfLe` is an
  -- isomorphism and the kernel factor is `1`
  rw [card_stabilizer_eq_card_ker_mul_card_stabilizer (Subgroup.subgroupOfEquivOfLe hle).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hle).surjective a
      -- both groups act through the same element of `G`; `Subgroup.smul_def` unfolds the two
      -- `Subgroup.instMulAction` layers and `subgroupOfEquivOfLe`'s structure projection, rather
      -- than leaving that chain to `rfl`
      fun g ↦ by simp [Subgroup.smul_def],
    MonoidHom.ker_eq_bot _ (Subgroup.subgroupOfEquivOfLe hle).injective]
  simp

open _root_.MulAction in
open scoped Pointwise in
/-- **The stabiliser of a coset and the stabiliser of the translated point have the same order.**
The class of `g` in `G ⧸ H` is stabilised inside `stabilizer G p` by exactly as many elements as
`g⁻¹ • p` is stabilised by inside `H`.

Stated at the level of a single group acting on `α`; the two-group form used below is the instance
`G := ↥ℋ`, `H := 𝒢.subgroupOf ℋ`, `g := ↑h`. -/
-- Not `@[simp]`, tested: `simpNF` runs over
-- the whole library, so the downstream global `@[simp]`
-- `TauCeti.stabilizer_eq_mackeySubgroup_subgroupOf` rewrites the left-hand side to
-- `Nat.card ((mackeySubgroup g H (stabilizer G p)).subgroupOf (stabilizer G p))` regardless of
-- which module carries the attribute. The obstruction is that lemma, not this one's placement.
theorem card_stabilizer_coset_eq_card_stabilizer_inv_smul (H : Subgroup G) (p : α) (g : G) :
    Nat.card (stabilizer (↥(stabilizer G p)) ((g : G ⧸ H))) =
      Nat.card (stabilizer (↥H) (g⁻¹ • p)) := by
  -- conjugation by `g` is the bijection: an `x` fixing `p` and fixing the class of `g` satisfies
  -- `g⁻¹ * x * g ∈ H`, and that conjugate fixes `g⁻¹ • p`; conjugating back is the inverse
  refine Nat.card_congr ⟨fun x => ⟨⟨g⁻¹ * (x : G) * g, ?_⟩, ?_⟩,
    fun h => ⟨⟨g * (h : G) * g⁻¹, ?_⟩, ?_⟩, fun x => ?_, fun h => ?_⟩
  · -- the stabiliser of a coset is the conjugate subgroup, by `stabilizer_quotientGroup_mk`
    have hx := x.2
    rw [mem_stabilizer_iff, Subgroup.smul_def, ← mem_stabilizer_iff,
      stabilizer_quotientGroup_mk, mem_conj_smul] at hx
    exact hx
  · -- `g⁻¹ * x * g` sends `g⁻¹ • p` to `g⁻¹ • (x • p)`, and `x` fixes `p`
    have hp := (x : ↥(stabilizer G p)).2
    rw [mem_stabilizer_iff] at hp
    rw [mem_stabilizer_iff, Subgroup.smul_def, mul_smul, mul_smul, smul_inv_smul, hp]
  · -- `hh` is stated for the `↥H`-action; `Subgroup.smul_def` puts it in the `G`-action the
    -- conjugated element acts by
    have hh := h.2
    rw [mem_stabilizer_iff, Subgroup.smul_def] at hh
    rw [mem_stabilizer_iff, mul_smul, mul_smul, hh, smul_inv_smul]
  · -- same route back: membership in the conjugate subgroup is `h ∈ H` after cancellation
    rw [mem_stabilizer_iff, Subgroup.smul_def, ← mem_stabilizer_iff,
      stabilizer_quotientGroup_mk, mem_conj_smul]
    simp [mul_assoc]
  · exact Subtype.ext (Subtype.ext (by simp [mul_assoc]))
  · exact Subtype.ext (Subtype.ext (by simp [mul_assoc]))

end TauCeti

namespace MonoidHom

open Equiv

variable {G α : Type*} [Group G]

/-- If a point has trivial stabiliser under the image of a permutation representation, then its
stabiliser in the source is the kernel of the representation. -/
theorem comap_stabilizer_eq_ker (ρ : G →* Perm α) (i : α)
    (hi : MulAction.stabilizer ρ.range i = ⊥) :
    (MulAction.stabilizer (Perm α) i).comap ρ = ρ.ker := by
  ext g
  rw [Subgroup.mem_comap, MulAction.mem_stabilizer_iff, MonoidHom.mem_ker]
  refine ⟨fun hg => ?_, fun hg => by rw [hg, one_smul]⟩
  let h : ρ.range := ⟨ρ g, MonoidHom.mem_range.mpr ⟨g, rfl⟩⟩
  have hh : h = 1 := by
    rw [← Subgroup.mem_bot, ← hi, MulAction.mem_stabilizer_iff]
    exact hg
  exact congrArg Subtype.val hh

/-- For a transitive permutation representation, a point stabiliser is normal in the source
exactly when the image acts freely. -/
theorem normal_comap_stabilizer_iff_isCancelSMul (ρ : G →* Perm α)
    (hρ : MulAction.IsPretransitive ρ.range α) (i : α) :
    ((MulAction.stabilizer (Perm α) i).comap ρ).Normal ↔ IsCancelSMul ρ.range α := by
  refine ⟨fun hN => ?_, fun hfree => ?_⟩
  · set K := (MulAction.stabilizer (Perm α) i).comap ρ
    have hK : ∀ (g : G) (j : α), ρ g j = j ↔ g ∈ K := by
      intro g j
      obtain ⟨h, hh⟩ := hρ.exists_smul_eq i j
      obtain ⟨k, hk⟩ : (h : Perm α) ∈ ρ.range := h.2
      have hki : ρ k i = j := hk ▸ hh
      have hconj : k⁻¹ * g * k ∈ K ↔ ρ g j = j := by
        rw [Subgroup.mem_comap, MulAction.mem_stabilizer_iff]
        simp only [map_mul, map_inv, Perm.smul_def, Perm.mul_apply]
        calc
          (ρ k)⁻¹ (ρ g (ρ k i)) = i ↔ ρ g (ρ k i) = ρ k i := by
            rw [Perm.inv_eq_iff_eq]
          _ ↔ ρ g j = j := by rw [hki]
      rw [← hconj]
      exact ⟨fun hg => by simpa [mul_assoc] using hN.conj_mem _ hg k,
        fun hg => by simpa using hN.conj_mem _ hg k⁻¹⟩
    refine isCancelSMul_iff_stabilizer_eq_bot.mpr fun j => ?_
    refine (Subgroup.eq_bot_iff_forall _).mpr fun h hh => ?_
    obtain ⟨g, hg⟩ : (h : Perm α) ∈ ρ.range := h.2
    have hgj : ρ g j = j := hg ▸ hh
    refine Subtype.ext <| hg ▸ Equiv.ext fun k => ?_
    exact (hK g k).mpr ((hK g j).mp hgj)
  · rw [comap_stabilizer_eq_ker ρ i (IsCancelSMul.stabilizer_eq_bot i)]
    infer_instance

end MonoidHom

end
