/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Iso
public import TauCeti.Combinatorics.Graph.Serre.Tree

/-!
# Local criteria for morphisms of Serre graphs

A morphism of Serre graphs `f : Γ → Δ` is locally injective when two darts with a common source
and the same image are equal. Such a morphism maps reduced paths to reduced paths
(`SerreGraph.Hom.isReduced_mapPath`), so its source is acyclic when its target is
(`SerreGraph.IsAcyclic.comap`), and from a preconnected graph to an acyclic graph it is injective
on vertices and on darts (`SerreGraph.Hom.mapV_injective_of_isAcyclic`,
`SerreGraph.Hom.mapE_injective_of_isAcyclic`). Dually, a morphism from a nonempty graph to a
preconnected graph is surjective on vertices and on darts as soon as every dart issuing from a
vertex of its image is the image of a dart (`SerreGraph.Hom.mapV_surjective_of_preconnected`,
`SerreGraph.Hom.mapE_surjective_of_preconnected`).

Hence a morphism from a nonempty preconnected graph to a preconnected acyclic graph that maps the
darts issuing from each vertex bijectively onto those issuing from its image is bijective on
vertices and on darts, so it is an isomorphism (`SerreGraph.Iso.ofLocallyBijective`). Isomorphic
graphs are acyclic together and trees together (`SerreGraph.Iso.isAcyclic_iff`,
`SerreGraph.Iso.isTree_iff`). In the structure theorem for groups acting on trees, these criteria
compare the tree with the Bass–Serre tree of the quotient graph of groups.

Acyclicity can also be read from a height function on the vertices with values in a linear order
(`SerreGraph.isAcyclic_of_height`): if every vertex is the source of at most one dart whose target
is not higher, then a reduced path first goes down and then strictly up, so a reduced closed path
is empty.

## References

* J.-P. Serre, *Trees*, Chapter I, §2.2 and §5.4.
-/

public section

universe u v w x

namespace TauCeti
namespace SerreGraph

variable {Γ : SerreGraph.{u, v}} {Δ : SerreGraph.{w, x}}

namespace Hom

/-- A morphism that is injective on the darts issuing from each vertex maps reduced paths to
reduced paths. -/
theorem isReduced_mapPath (f : Γ.Hom Δ)
    (hf : ∀ e e' : Γ.E, Γ.src e = Γ.src e' → f.mapE e = f.mapE e' → e = e')
    {a b : Γ.V} (p : Γ.Path a b) (hp : Path.IsReduced Γ p) :
    Path.IsReduced Δ (f.toPrefunctor.mapPath p) := by
  induction p with
  | nil => exact Path.isReduced_nil Δ _
  | cons p e ih =>
    cases p with
    | nil => exact Path.isReduced_toPath Δ _
    | cons p d =>
      obtain ⟨hpd, hne⟩ := (Path.isReduced_cons_cons Γ p d e).mp hp
      refine (Path.isReduced_cons_cons Δ _ _ _).mpr
        ⟨ih hpd, fun he => hne (hf _ _ (by simp [e.2.1, d.2.2]) ?_)⟩
      rwa [Hom.toPrefunctor_map_val, Hom.toPrefunctor_map_val, ← f.map_rev] at he

end Hom

/-- The source of a morphism into an acyclic graph that is injective on the darts issuing from
each vertex is acyclic. -/
theorem IsAcyclic.comap (f : Γ.Hom Δ)
    (hf : ∀ e e' : Γ.E, Γ.src e = Γ.src e' → f.mapE e = f.mapE e' → e = e')
    (h : Δ.IsAcyclic) : Γ.IsAcyclic := by
  refine (isAcyclic_iff Γ).mpr fun a p hp => ?_
  have hd := congrArg (Path.darts Δ) ((isAcyclic_iff Δ).mp h _ _ (f.isReduced_mapPath hf p hp))
  rw [Hom.darts_mapPath, Path.darts_nil, List.map_eq_nil_iff] at hd
  exact Quiver.Path.eq_nil_of_length_zero p (by rw [← Path.length_darts, hd, List.length_nil])

namespace Hom

/-- A morphism from a preconnected graph to an acyclic graph that is injective on the darts
issuing from each vertex is injective on vertices. -/
theorem mapV_injective_of_isAcyclic (f : Γ.Hom Δ) (hΓ : Γ.Preconnected) (hΔ : Δ.IsAcyclic)
    (hf : ∀ e e' : Γ.E, Γ.src e = Γ.src e' → f.mapE e = f.mapE e' → e = e') :
    Function.Injective f.mapV := by
  -- A reduced path of `Δ` whose ends coincide is empty.
  have key {x y : Δ.V} (q : Δ.Path x y) (hq : Path.IsReduced Δ q) (hxy : x = y) :
      Path.darts Δ q = [] := by
    subst hxy
    rw [(isAcyclic_iff Δ).mp hΔ _ q hq, Path.darts_nil]
  intro a b hab
  obtain ⟨p⟩ := Γ.preconnected_iff.mp hΓ a b
  -- The image of the reduced path from `a` to `b` is a reduced closed path, hence empty.
  have hd := key _ (f.isReduced_mapPath hf _ (Path.isReduced_reduce Γ p)) hab
  rw [Hom.darts_mapPath, List.map_eq_nil_iff] at hd
  exact Path.eq_of_darts_eq_nil Γ _ hd

/-- A morphism from a preconnected graph to an acyclic graph that is injective on the darts
issuing from each vertex is injective on darts. -/
theorem mapE_injective_of_isAcyclic (f : Γ.Hom Δ) (hΓ : Γ.Preconnected) (hΔ : Δ.IsAcyclic)
    (hf : ∀ e e' : Γ.E, Γ.src e = Γ.src e' → f.mapE e = f.mapE e' → e = e') :
    Function.Injective f.mapE := fun e e' h =>
  hf e e' (f.mapV_injective_of_isAcyclic hΓ hΔ hf (by rw [← f.map_src, h, f.map_src])) h

/-- A morphism from a nonempty graph to a preconnected graph is surjective on vertices when every
dart issuing from a vertex of its image is the image of a dart. -/
theorem mapV_surjective_of_preconnected (f : Γ.Hom Δ) [Nonempty Γ.V] (hΔ : Δ.Preconnected)
    (hf : ∀ d : Δ.E, Δ.src d ∈ Set.range f.mapV → d ∈ Set.range f.mapE) :
    Function.Surjective f.mapV := by
  intro b
  obtain ⟨a₀⟩ := ‹Nonempty Γ.V›
  obtain ⟨p⟩ := Δ.preconnected_iff.mp hΔ (f.mapV a₀) b
  induction p with
  | nil => exact ⟨a₀, rfl⟩
  | cons _ d ih =>
    obtain ⟨e, he⟩ := hf d.1 (by rwa [d.2.1])
    exact ⟨Γ.tgt e, by rw [← f.map_tgt, he, d.2.2]⟩

/-- A morphism from a nonempty graph to a preconnected graph is surjective on darts when every
dart issuing from a vertex of its image is the image of a dart. -/
theorem mapE_surjective_of_preconnected (f : Γ.Hom Δ) [Nonempty Γ.V] (hΔ : Δ.Preconnected)
    (hf : ∀ d : Δ.E, Δ.src d ∈ Set.range f.mapV → d ∈ Set.range f.mapE) :
    Function.Surjective f.mapE := fun d =>
  hf d (f.mapV_surjective_of_preconnected hΔ hf (Δ.src d))

end Hom

namespace Iso

/-- A morphism from a nonempty preconnected graph to a preconnected acyclic graph that maps the
darts issuing from each vertex bijectively onto the darts issuing from its image is an
isomorphism. -/
noncomputable def ofLocallyBijective (f : Γ.Hom Δ) [Nonempty Γ.V] (hΓ : Γ.Preconnected)
    (hΔ : Δ.Preconnected) (hΔ' : Δ.IsAcyclic)
    (hinj : ∀ e e' : Γ.E, Γ.src e = Γ.src e' → f.mapE e = f.mapE e' → e = e')
    (hsurj : ∀ (a : Γ.V) (d : Δ.E), Δ.src d = f.mapV a → ∃ e : Γ.E, Γ.src e = a ∧ f.mapE e = d) :
    Γ.Iso Δ :=
  have hf : ∀ d : Δ.E, Δ.src d ∈ Set.range f.mapV → d ∈ Set.range f.mapE :=
    fun d ⟨a, ha⟩ => (hsurj a d ha.symm).imp fun _ => And.right
  f.toIso ⟨f.mapV_injective_of_isAcyclic hΓ hΔ' hinj, f.mapV_surjective_of_preconnected hΔ hf⟩
    ⟨f.mapE_injective_of_isAcyclic hΓ hΔ' hinj, f.mapE_surjective_of_preconnected hΔ hf⟩

section ofLocallyBijective

variable (f : Γ.Hom Δ) [Nonempty Γ.V] (hΓ : Γ.Preconnected) (hΔ : Δ.Preconnected)
  (hΔ' : Δ.IsAcyclic) (hinj : ∀ e e' : Γ.E, Γ.src e = Γ.src e' → f.mapE e = f.mapE e' → e = e')
  (hsurj : ∀ (a : Γ.V) (d : Δ.E), Δ.src d = f.mapV a → ∃ e : Γ.E, Γ.src e = a ∧ f.mapE e = d)

@[simp] theorem ofLocallyBijective_equivV_apply (a : Γ.V) :
    (ofLocallyBijective f hΓ hΔ hΔ' hinj hsurj).equivV a = f.mapV a :=
  Hom.toIso_equivV_apply f _ _ a

@[simp] theorem ofLocallyBijective_equivE_apply (e : Γ.E) :
    (ofLocallyBijective f hΓ hΔ hΔ' hinj hsurj).equivE e = f.mapE e :=
  Hom.toIso_equivE_apply f _ _ e

@[simp] theorem ofLocallyBijective_toHom :
    (ofLocallyBijective f hΓ hΔ hΔ' hinj hsurj).toHom = f :=
  Hom.toIso_toHom f _ _

end ofLocallyBijective

/-- Isomorphic Serre graphs are acyclic together. -/
theorem isAcyclic_iff (φ : Γ.Iso Δ) : Γ.IsAcyclic ↔ Δ.IsAcyclic :=
  ⟨.comap φ.symm.toHom fun _ _ _ h => by simpa using h,
    .comap φ.toHom fun _ _ _ h => by simpa using h⟩

/-- Isomorphic Serre graphs are trees together. -/
theorem isTree_iff (φ : Γ.Iso Δ) : Γ.IsTree ↔ Δ.IsTree :=
  (SerreGraph.isTree_iff Γ).trans <|
    (and_congr φ.connected_iff.symm φ.isAcyclic_iff).trans (SerreGraph.isTree_iff Δ).symm

end Iso

section Height

variable {α : Type*} [LinearOrder α] (height : Γ.V → α)
  (h : ∀ e e' : Γ.E, Γ.src e = Γ.src e' → height (Γ.tgt e) ≤ height (Γ.src e) →
    height (Γ.tgt e') ≤ height (Γ.src e') → e = e')
include h

omit h in
/-- Along a path none of whose darts goes down, the height does not decrease. -/
private theorem height_le_of_forall_mem_darts {a b : Γ.V} (p : Γ.Path a b)
    (hp : ∀ e ∈ Path.darts Γ p, height (Γ.src e) ≤ height (Γ.tgt e)) : height a ≤ height b := by
  induction p with
  | nil => exact le_rfl
  | cons p e ih =>
    obtain ⟨e, rfl, rfl⟩ := e
    exact (ih fun d hd => hp d (by simp [hd])).trans (hp e (by simp))

/-- A reduced path first follows darts that do not go up and then darts that go strictly up. -/
private theorem exists_eq_comp_of_isReduced {a b : Γ.V} (p : Γ.Path a b)
    (hp : Path.IsReduced Γ p) :
    ∃ (c : Γ.V) (q : Γ.Path a c) (r : Γ.Path c b), p = q.comp r ∧
      (∀ e ∈ Path.darts Γ q, height (Γ.tgt e) ≤ height (Γ.src e)) ∧
      ∀ e ∈ Path.darts Γ r, height (Γ.src e) < height (Γ.tgt e) := by
  induction p with
  | nil => exact ⟨_, .nil, .nil, rfl, by simp, by simp⟩
  | cons p e ih =>
    obtain ⟨c, q, r, rfl, hq, hr⟩ := ih (hp.of_cons Γ)
    by_cases he : height (Γ.src e.1) < height (Γ.tgt e.1)
    · refine ⟨c, q, r.cons e, rfl, hq, ?_⟩
      simp only [Path.darts_cons, List.mem_append, List.mem_singleton]
      rintro d (hd | rfl)
      exacts [hr d hd, he]
    · cases r with
      | nil =>
        refine ⟨_, q.cons e, .nil, rfl, ?_, by simp⟩
        simp only [Path.darts_cons, List.mem_append, List.mem_singleton]
        rintro d (hd | rfl)
        exacts [hq d hd, not_lt.mp he]
      | cons r d =>
        -- The reverse of `d` and the dart `e` leave the same vertex without going up.
        refine absurd (h e.1 (Γ.rev d.1) (by simp [e.2.1, d.2.2]) (not_lt.mp he) ?_)
          ((Path.isReduced_cons_cons Γ (q.comp r) d e).mp hp).2
        simpa using (hr d.1 (by simp)).le

/-- A reduced closed path none of whose darts goes down is empty. -/
private theorem eq_nil_of_forall_mem_darts {c : Γ.V} (q : Γ.Path c c)
    (hq : Path.IsReduced Γ q)
    (hle : ∀ e ∈ Path.darts Γ q, height (Γ.src e) ≤ height (Γ.tgt e)) : q = .nil := by
  cases q with
  | nil => rfl
  | cons q e =>
    exfalso
    cases q with
    | nil =>
      -- A loop and its reverse leave the same vertex without going up.
      refine Γ.rev_ne e.1 (h _ _ ?_ ?_ ?_).symm <;> simp [e.2.1, e.2.2]
    | cons q d =>
      have hred := ((Path.isReduced_cons_cons Γ q d e).mp hq).2
      obtain ⟨d, rfl, rfl⟩ := d
      obtain ⟨e, he, rfl⟩ := e
      have hq' := height_le_of_forall_mem_darts height q fun d hd => hle d (by simp [hd])
      have hd := hle d (by simp)
      -- The dart `e` and the reverse of `d` leave the same vertex without going up.
      exact hred (h _ _ (by simpa using he) (by simpa [he] using hq'.trans hd) (by simpa using hd))

/-- Two paths with the same ends are equal if the darts of the first go strictly up and the second
is reduced with no dart going down. -/
private theorem eq_of_forall_mem_darts {c u : Γ.V} (r q : Γ.Path c u)
    (hr : ∀ e ∈ Path.darts Γ r, height (Γ.src e) < height (Γ.tgt e))
    (hq : Path.IsReduced Γ q)
    (hle : ∀ e ∈ Path.darts Γ q, height (Γ.src e) ≤ height (Γ.tgt e)) : r = q := by
  induction r with
  | nil => exact (eq_nil_of_forall_mem_darts height h q hq hle).symm
  | cons r e ih =>
    have he := hr e.1 (by simp)
    cases q with
    | nil =>
      have hr' := height_le_of_forall_mem_darts height r fun d hd => (hr d (by simp [hd])).le
      rw [e.2.1, e.2.2] at he
      exact absurd (hr'.trans_lt he) (lt_irrefl _)
    | cons q d =>
      -- The reverses of the last darts leave the same vertex without going up.
      have hed : e.1 = d.1 := Γ.rev_injective <| h _ _ (by simp [e.2.2, d.2.2])
        (by simpa using he.le) (by simpa using hle d.1 (by simp))
      obtain rfl := e.2.1.symm.trans ((congrArg Γ.src hed).trans d.2.1)
      obtain rfl : e = d := Subtype.ext hed
      rw [ih q (fun d hd => hr d (by simp [hd])) (hq.of_cons Γ)
        fun d hd => hle d (by simp [hd])]

end Height

/-- A Serre graph is acyclic if, for a height function on its vertices with values in a linear
order, every vertex is the source of at most one dart whose target is not higher. -/
theorem isAcyclic_of_height (Γ : SerreGraph.{u, v}) {α : Type*} [LinearOrder α] (height : Γ.V → α)
    (h : ∀ e e' : Γ.E, Γ.src e = Γ.src e' → height (Γ.tgt e) ≤ height (Γ.src e) →
      height (Γ.tgt e') ≤ height (Γ.src e') → e = e') : Γ.IsAcyclic := by
  refine (isAcyclic_iff Γ).mpr fun u p hp => ?_
  obtain ⟨c, q, r, rfl, hq, hr⟩ := exists_eq_comp_of_isReduced height h p hp
  -- The two halves of the path, read from the bottom, coincide.
  obtain rfl : r = q.reverse := eq_of_forall_mem_darts height h r q.reverse hr
    ((Path.isReduced_reverse Γ q).mpr (hp.of_comp_left Γ)) <| by
      simp only [Path.darts_reverse, List.mem_map, List.mem_reverse]
      rintro _ ⟨e, he, rfl⟩
      simpa using hq e he
  exact (Path.reduce_eq_self_of_isReduced Γ _ hp).symm.trans (Path.reduce_comp_reverse Γ q)

end SerreGraph
end TauCeti
