/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Aut
public import TauCeti.GroupTheory.GraphOfGroups.Path

/-!
# The Bass–Serre graph of a graph of groups

For a graph of groups `𝔸` over a Serre graph `Γ` and a base vertex `v₀`, the Bass–Serre graph
`X(𝔸, v₀)` is the Serre graph whose

* vertices are the classes `p A_a` of `𝔸`-paths `p` from `v₀` to a vertex `a`, where two paths
  `p` and `p'` ending at `a` give the same vertex when `p ∼ p' g` for some `g ∈ A_a`;
* darts over a dart `e` of `Γ` are the classes `p α_e(A_e)` of `𝔸`-paths `p` from `v₀` to the
  source of `e`, where `p` and `p'` give the same dart when `p ∼ p' α_e(c)` for some `c ∈ A_e`.

The dart over `e` represented by `p` runs from `p A_{src e}` to `p e A_{tgt e}`, and its reverse
is the dart over `rev e` represented by `p e`. So two vertices are adjacent exactly when they
can be written `p A_a` and `p g e A_b` with `g ∈ A_a` and `e` a dart from `a` to `b`.

The fundamental group `π₁(𝔸, v₀)` acts on `X(𝔸, v₀)` by concatenation on the left,
`q · p A_a = q p A_a`, by graph automorphisms (`GraphOfGroups.bassSerreAction`) and without
inversions. The projection `p A_a ↦ a` is a morphism of Serre graphs to `Γ`, and two vertices,
or two darts, lie in the same orbit exactly when they lie over the same vertex or dart of `Γ`:
the orbits are the nonempty fibres of the projection. The stabilizer of the vertex `p A_a` is
the image `p A_a p⁻¹` of `π₁.vertexHom p`, and the stabilizer of the dart represented by `p`
over `e` is `p α_e(A_e) p⁻¹`. These descriptions hold for every graph of groups; that
`X(𝔸, v₀)` is a tree, and that `π₁.vertexHom p` is injective, so that the stabilizers are copies
of the vertex and edge groups, are consequences of the normal form theorem.

## Main definitions

* `TauCeti.GraphOfGroups.bassSerreGraph`: the Bass–Serre graph `X(𝔸, v₀)`.
* `TauCeti.GraphOfGroups.BassSerreVertex`, `TauCeti.GraphOfGroups.BassSerreDart`: the vertices
  and darts of `X(𝔸, v₀)`, with constructors `mk` and eliminators `lift` and `induction_on`.
* `TauCeti.GraphOfGroups.bassSerreAction`: the action of `π₁(𝔸, v₀)` as a homomorphism to the
  automorphism group of `X(𝔸, v₀)`.
* `TauCeti.GraphOfGroups.bassSerreProj`: the projection `X(𝔸, v₀) → Γ`.

## Main results

* `TauCeti.GraphOfGroups.BassSerreVertex.mk_eq_mk_iff`,
  `TauCeti.GraphOfGroups.BassSerreDart.mk_eq_mk_iff`: when two paths give the same vertex or dart.
* `TauCeti.GraphOfGroups.BassSerreDart.smul_ne_rev`: the action has no inversions.
* `TauCeti.GraphOfGroups.BassSerreVertex.mem_orbit_iff_proj_eq`,
  `TauCeti.GraphOfGroups.BassSerreDart.mem_orbit_iff_proj_eq`: two vertices or darts lie in the
  same orbit exactly when they have the same image in `Γ`.
* `TauCeti.GraphOfGroups.BassSerreVertex.stabilizer_mk`,
  `TauCeti.GraphOfGroups.BassSerreDart.stabilizer_mk`: the vertex and dart stabilizers.
* Over a graph without edges the Bass–Serre graph has exactly one vertex and no darts.

## References

* I. Kapovich, R. Weidmann, A. Myasnikov, *Foldings, graphs of groups and the membership problem*,
  Internat. J. Algebra Comput. 15 (2005), §2, Definition 2.5 and the paragraphs after it.
* J.-P. Serre, *Trees*, Chapter I, §5.3, Theorem 12.
-/

public section

universe u v w x

namespace TauCeti

namespace GraphOfGroups

open _root_.MulAction

variable {Γ : SerreGraph.{u, v}} (𝔸 : GraphOfGroups.{u, v, w, x} Γ)

/-! ### Paths modulo a subgroup at the endpoint -/

/- For vertices `t i` of `Γ` and subgroups `H i` of the vertex groups `A_{t i}`, two `𝔸`-paths
from `v₀` ending at the same `t i` are related when `p ∼ q h` for some `h ∈ H i`. -/
private inductive CosetRel {ι : Type*} (t : ι → Γ.V) (H : ∀ i, Subgroup (𝔸.vertexGroup (t i)))
    (v₀ : Γ.V) : (Σ i, 𝔸.Path ⟨v₀⟩ ⟨t i⟩) → (Σ i, 𝔸.Path ⟨v₀⟩ ⟨t i⟩) → Prop
  | intro {i : ι} (p q : 𝔸.Path ⟨v₀⟩ ⟨t i⟩) (h : 𝔸.vertexGroup (t i)) (hh : h ∈ H i)
      (hpq : p.Homotopic (q.cons (Letter.vertex h))) : CosetRel t H v₀ ⟨i, p⟩ ⟨i, q⟩

variable {𝔸} {ι : Type*} {t : ι → Γ.V} {H : ∀ i, Subgroup (𝔸.vertexGroup (t i))} {v₀ : Γ.V}

private theorem cosetRel_equivalence : Equivalence (CosetRel 𝔸 t H v₀) where
  refl := fun ⟨i, p⟩ ↦ .intro p p 1 (H i).one_mem (Path.Homotopic.one p).symm
  symm := by
    rintro _ _ ⟨p, q, h, hh, hpq⟩
    have hq := Path.Homotopic.cons_cons_reverse q (Letter.vertex h)
    rw [Letter.reverse_vertex] at hq
    exact .intro q p h⁻¹ ((H _).inv_mem hh) ((hpq.cons _).trans hq).symm
  trans := by
    rintro _ _ _ ⟨p, q, h, hh, hpq⟩ hqr
    obtain ⟨_, r, k, hk, hqr⟩ := hqr
    exact .intro p r (k * h) ((H _).mul_mem hk hh) (hpq.trans ((hqr.cons _).trans (.mul r k h)))

private theorem quot_mk_eq_quot_mk_iff {i : ι} {p q : 𝔸.Path ⟨v₀⟩ ⟨t i⟩} :
    Quot.mk (CosetRel 𝔸 t H v₀) ⟨i, p⟩ = Quot.mk _ ⟨i, q⟩ ↔
      ∃ h ∈ H i, p.Homotopic (q.cons (Letter.vertex h)) := by
  refine ⟨fun hpq ↦ ?_, fun ⟨h, hh, hpq⟩ ↦ Quot.sound (.intro p q h hh hpq)⟩
  obtain ⟨_, _, h, hh, hpq⟩ := cosetRel_equivalence.eqvGen_iff.1 (Quot.eqvGen_exact hpq)
  exact ⟨h, hh, hpq⟩

private theorem quot_mk_eq_quot_mk_of_homotopic {i : ι} {p q : 𝔸.Path ⟨v₀⟩ ⟨t i⟩}
    (h : p.Homotopic q) : Quot.mk (CosetRel 𝔸 t H v₀) ⟨i, p⟩ = Quot.mk _ ⟨i, q⟩ :=
  quot_mk_eq_quot_mk_iff.2 ⟨1, (H i).one_mem, h.trans (Path.Homotopic.one q).symm⟩

/- The action of `π₁(𝔸, v₀)` on the classes by concatenation on the left, with its orbits and
stabilizers; the action on the Bass–Serre graph is built from its two instances, on the vertices
and on the darts. -/

-- The index `i` of the class of a path ending at `t i`.
private def cosetIndex : Quot (CosetRel 𝔸 t H v₀) → ι :=
  Quot.lift Sigma.fst fun _ _ ⟨_, _, _, _, _⟩ ↦ rfl

-- `π₁(𝔸, v₀)` acts on the classes by concatenation on the left, `q · p H_i = q p H_i`.
private instance : SMul (π₁ 𝔸 v₀) (Quot (CosetRel 𝔸 t H v₀)) where
  smul := π₁.lift (fun q ↦ Quot.lift (fun y ↦ Quot.mk _ ⟨y.1, q.comp y.2⟩)
      fun _ _ ⟨_, _, h, hh, hpq⟩ ↦ quot_mk_eq_quot_mk_iff.2 ⟨h, hh, by simpa using hpq.comp_left q⟩)
    fun _ _ h ↦ funext <| Quot.ind fun ⟨_, p⟩ ↦ quot_mk_eq_quot_mk_of_homotopic (h.comp_right p)

private theorem mk_smul_quot_mk (q : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩) {i : ι} (p : 𝔸.Path ⟨v₀⟩ ⟨t i⟩) :
    π₁.mk q • Quot.mk (CosetRel 𝔸 t H v₀) ⟨i, p⟩ = Quot.mk _ ⟨i, q.comp p⟩ :=
  congrFun (π₁.lift_mk _ _ q) _

private instance : MulAction (π₁ 𝔸 v₀) (Quot (CosetRel 𝔸 t H v₀)) where
  one_smul := Quot.ind fun ⟨_, p⟩ ↦ by rw [← π₁.mk_nil, mk_smul_quot_mk, Quiver.Path.nil_comp]
  mul_smul g h := π₁.induction_on g fun q ↦ π₁.induction_on h fun r ↦ Quot.ind fun ⟨_, p⟩ ↦ by
    rw [← π₁.mk_comp, mk_smul_quot_mk, mk_smul_quot_mk, mk_smul_quot_mk, Quiver.Path.comp_assoc]

private theorem cosetIndex_smul (g : π₁ 𝔸 v₀) (x : Quot (CosetRel 𝔸 t H v₀)) :
    cosetIndex (g • x) = cosetIndex x := by
  induction g using π₁.induction_on with | h q => ?_
  induction x using Quot.ind with | mk x => rw [mk_smul_quot_mk q x.2]; rfl

-- Two classes lie in the same orbit exactly when they have the same index.
private theorem mem_orbit_iff_cosetIndex {x y : Quot (CosetRel 𝔸 t H v₀)} :
    y ∈ orbit (π₁ 𝔸 v₀) x ↔ cosetIndex y = cosetIndex x := by
  refine ⟨fun ⟨g, hg⟩ ↦ hg ▸ cosetIndex_smul g x, fun h ↦ ?_⟩
  induction x using Quot.ind with | mk x => ?_
  induction y using Quot.ind with | mk y => ?_
  obtain ⟨i, p⟩ := x
  obtain ⟨_, q⟩ := y
  obtain rfl := h
  exact ⟨π₁.mk (q.comp p.reverse), (mk_smul_quot_mk _ p).trans
    (quot_mk_eq_quot_mk_of_homotopic (Path.homotopic_comp_reverse_iff.1 (.refl _)))⟩

-- The stabilizer of the class `p H_i` is `p H_i p⁻¹`.
private theorem stabilizer_quot_mk {i : ι} (p : 𝔸.Path ⟨v₀⟩ ⟨t i⟩) :
    stabilizer (π₁ 𝔸 v₀) (Quot.mk (CosetRel 𝔸 t H v₀) ⟨i, p⟩) = (H i).map (π₁.vertexHom p) := by
  ext g
  induction g using π₁.induction_on with | h q => ?_
  simp only [mem_stabilizer_iff, mk_smul_quot_mk, quot_mk_eq_quot_mk_iff, Subgroup.mem_map,
    π₁.vertexHom_apply, Path.comp_ofVertex, π₁.mk_eq_mk_iff]
  exact exists_congr fun _ ↦ and_congr_right fun _ ↦
    Path.homotopic_comp_reverse_iff.symm.trans ⟨.symm, .symm⟩

/-! ### The Bass–Serre graph -/

-- The source `p A_{src e}` of the dart over `e` given by `p`.
private def dartSrc : Quot (CosetRel 𝔸 Γ.src (fun e ↦ (𝔸.α e).range) v₀) →
    Quot (CosetRel 𝔸 (fun a ↦ a) (fun _ ↦ ⊤) v₀) :=
  Quot.lift (fun y ↦ Quot.mk _ ⟨Γ.src y.1, y.2⟩) fun _ _ ⟨_, _, h, _, hpq⟩ ↦
    quot_mk_eq_quot_mk_iff.2 ⟨h, Subgroup.mem_top h, hpq⟩

-- The reverse of the dart over `e` given by `p`: the dart over `rev e` given by `p e`.
private def dartRev : Quot (CosetRel 𝔸 Γ.src (fun e ↦ (𝔸.α e).range) v₀) →
    Quot (CosetRel 𝔸 Γ.src (fun e ↦ (𝔸.α e).range) v₀) :=
  Quot.lift (fun y ↦ Quot.mk _ ⟨Γ.rev y.1, y.2.cons (Letter.dart (Γ.dart y.1))⟩) fun _ _ h ↦ by
    obtain ⟨p, q, _, ⟨c, rfl⟩, h⟩ := h
    -- `p e ∼ q α_e(c) e ∼ q e ω_e(c)`, and `ω_e(c) = α_{rev e}(c)`.
    refine quot_mk_eq_quot_mk_iff.2 ⟨_, ⟨(MulEquiv.cast (Γ.toGeomEdge_rev _)).symm c, rfl⟩, ?_⟩
    rw [α_rev_apply, MulEquiv.apply_symm_apply]
    exact (h.cons _).trans (Path.Homotopic.dart_ω _ c q).symm

-- Appending two darts with the same underlying dart of `Γ` gives the same path, up to the
-- identification of their endpoints.
private theorem heq_cons_dart {y : 𝔸.LetterVertex} {a b b' : Γ.V} (q : 𝔸.Path y ⟨a⟩) (f : a ⟶ b)
    (f' : a ⟶ b') (h : f.val = f'.val) : q.cons (Letter.dart f) ≍ q.cons (Letter.dart f') := by
  obtain ⟨e, rfl, rfl⟩ := f
  obtain ⟨e', _, rfl⟩ := f'
  obtain rfl : e = e' := h
  rfl

-- Reversal of darts is an involution.
private theorem dartRev_dartRev (d : Quot (CosetRel 𝔸 Γ.src (fun e ↦ (𝔸.α e).range) v₀)) :
    dartRev (dartRev d) = d := by
  induction d using Quot.ind with | mk y => ?_
  obtain ⟨e, p⟩ := y
  -- The dart `rev (rev e)` is only propositionally equal to `e`: transport the representative.
  have hσ : (⟨Γ.rev (Γ.rev e), (p.cons (Letter.dart (Γ.dart e))).cons
        (Letter.dart (Γ.dart (Γ.rev e)))⟩ : Σ e : Γ.E, 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) =
      ⟨e, (p.cons (Letter.dart (Γ.dart e))).cons (Letter.dart (Quiver.reverse (Γ.dart e)))⟩ :=
    Sigma.ext (Γ.rev_rev e) (heq_cons_dart _ _ _ (by simp))
  exact (congrArg (Quot.mk _) hσ).trans
    (quot_mk_eq_quot_mk_of_homotopic (Path.Homotopic.dart_reverse p (Γ.dart e)))

-- No dart is its own reverse: the reverse of a dart over `e` lies over `rev e ≠ e`.
private theorem dartRev_ne (d : Quot (CosetRel 𝔸 Γ.src (fun e ↦ (𝔸.α e).range) v₀)) :
    dartRev d ≠ d := by
  induction d using Quot.ind with | mk y => exact fun h ↦ Γ.rev_ne y.1 (congrArg cosetIndex h)

variable (𝔸 v₀) in
/-- The Bass–Serre graph `X(𝔸, v₀)` of a graph of groups `𝔸` at a base vertex `v₀`. Its vertices
are the classes `p A_a` of `𝔸`-paths `p` from `v₀` to a vertex `a`, where two paths `p` and `p'`
ending at `a` give the same vertex when `p ∼ p' g` for some `g ∈ A_a`. Its darts over a dart `e`
of `Γ` are the classes `p α_e(A_e)` of `𝔸`-paths `p` from `v₀` to the source of `e`, where `p`
and `p'` give the same dart when `p ∼ p' α_e(c)` for some `c ∈ A_e`. The dart over `e` given by
`p` runs from `p A_{src e}` to `p e A_{tgt e}`, and its reverse is the dart over `rev e` given by
`p e`. -/
def bassSerreGraph : SerreGraph.{max u v w, max u v w} where
  V := Quot (CosetRel 𝔸 (fun a ↦ a) (fun _ ↦ ⊤) v₀)
  E := Quot (CosetRel 𝔸 Γ.src (fun e ↦ (𝔸.α e).range) v₀)
  src := dartSrc
  rev := dartRev
  rev_rev := dartRev_dartRev
  rev_ne := dartRev_ne

variable (𝔸) in
/-- The vertices of the Bass–Serre graph `X(𝔸, v₀)`: the classes `p A_a` of `𝔸`-paths `p` from
`v₀` to a vertex `a`. -/
abbrev BassSerreVertex (v₀ : Γ.V) : Type (max u v w) :=
  (𝔸.bassSerreGraph v₀).V

variable (𝔸) in
/-- The darts of the Bass–Serre graph `X(𝔸, v₀)`: for each dart `e` of `Γ`, the classes
`p α_e(A_e)` of `𝔸`-paths `p` from `v₀` to the source of `e`. -/
abbrev BassSerreDart (v₀ : Γ.V) : Type (max u v w) :=
  (𝔸.bassSerreGraph v₀).E

/-! ### Vertices -/

namespace BassSerreVertex

variable {a : Γ.V}

/-- The vertex `p A_a` of the Bass–Serre graph given by an `𝔸`-path `p` from `v₀` to `a`. -/
def mk (p : 𝔸.Path ⟨v₀⟩ ⟨a⟩) : 𝔸.BassSerreVertex v₀ :=
  Quot.mk _ ⟨a, p⟩

/-- Two paths ending at `a` give the same vertex exactly when `p ∼ q g` for some `g ∈ A_a`. -/
theorem mk_eq_mk_iff {p q : 𝔸.Path ⟨v₀⟩ ⟨a⟩} : mk p = mk q ↔
    ∃ g : 𝔸.vertexGroup a, p.Homotopic (q.cons (Letter.vertex g)) :=
  quot_mk_eq_quot_mk_iff.trans (by simp)

/-- Homotopic paths give the same vertex. -/
theorem mk_eq_mk_of_homotopic {p q : 𝔸.Path ⟨v₀⟩ ⟨a⟩} (h : p.Homotopic q) : mk p = mk q :=
  quot_mk_eq_quot_mk_of_homotopic h

/-- Appending a vertex group element to a path does not change its vertex, `p g A_a = p A_a`. -/
@[simp] theorem mk_cons_vertex (p : 𝔸.Path ⟨v₀⟩ ⟨a⟩) (g : 𝔸.vertexGroup a) :
    mk (p.cons (Letter.vertex g)) = mk p :=
  mk_eq_mk_iff.2 ⟨g, .refl _⟩

/-- The path given by an element `g` of the vertex group at `v₀` represents the base vertex,
`g A_{v₀} = A_{v₀}`. -/
@[simp] theorem mk_ofVertex (g : 𝔸.vertexGroup v₀) :
    mk (Path.ofVertex g) = mk (Quiver.Path.nil : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩) := by
  rw [Path.ofVertex_eq_nil_cons, mk_cons_vertex]

/-- Going along a dart and back does not change the vertex, `p f f⁻¹ A_a = p A_a`. -/
@[simp] theorem mk_cons_dart_cons_dart_reverse {b : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨a⟩) (f : a ⟶ b) :
    mk ((p.cons (Letter.dart f)).cons (Letter.dart (Quiver.reverse f))) = mk p :=
  mk_eq_mk_of_homotopic (.dart_reverse p f)

/-- Every vertex of the Bass–Serre graph is `p A_a` for some path `p`. -/
@[elab_as_elim] theorem induction_on {P : 𝔸.BassSerreVertex v₀ → Prop} (x : 𝔸.BassSerreVertex v₀)
    (h : ∀ (a : Γ.V) (p : 𝔸.Path ⟨v₀⟩ ⟨a⟩), P (mk p)) : P x :=
  Quot.ind (fun y ↦ h y.1 y.2) x

/-- A function `f` on `𝔸`-paths from `v₀` descends to the vertices of the Bass–Serre graph when
`f p = f q` whenever `p ∼ q g` for some `g ∈ A_a`, that is, when `f` is invariant under homotopy
and under appending a vertex group element to the path. -/
def lift {β : Sort*} (f : ∀ a : Γ.V, 𝔸.Path ⟨v₀⟩ ⟨a⟩ → β)
    (hf : ∀ (a : Γ.V) (p q : 𝔸.Path ⟨v₀⟩ ⟨a⟩) (g : 𝔸.vertexGroup a),
      p.Homotopic (q.cons (Letter.vertex g)) → f a p = f a q) : 𝔸.BassSerreVertex v₀ → β :=
  Quot.lift (fun y ↦ f y.1 y.2) fun _ _ h ↦ by
    obtain ⟨p, q, g, -, hpq⟩ := h
    exact hf _ p q g hpq

/-- `BassSerreVertex.lift f hf` computes `f` on representatives. -/
@[simp] theorem lift_mk {β : Sort*} (f : ∀ a : Γ.V, 𝔸.Path ⟨v₀⟩ ⟨a⟩ → β)
    (hf : ∀ (a : Γ.V) (p q : 𝔸.Path ⟨v₀⟩ ⟨a⟩) (g : 𝔸.vertexGroup a),
      p.Homotopic (q.cons (Letter.vertex g)) → f a p = f a q) (p : 𝔸.Path ⟨v₀⟩ ⟨a⟩) :
    lift f hf (mk p) = f a p :=
  (rfl)

/-- The vertex of `Γ` below a vertex `p A_a` of the Bass–Serre graph: the endpoint `a`. -/
def proj : 𝔸.BassSerreVertex v₀ → Γ.V :=
  cosetIndex

/-- The vertex `p A_a` lies over the endpoint `a` of `p`. -/
@[simp] theorem proj_mk (p : 𝔸.Path ⟨v₀⟩ ⟨a⟩) : (mk p).proj = a :=
  (rfl)

/-- The base vertex `A_{v₀}` of the Bass–Serre graph, given by the empty path at `v₀`. -/
instance : Inhabited (𝔸.BassSerreVertex v₀) :=
  ⟨mk (Quiver.Path.nil : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩)⟩

/-- The base vertex of the Bass–Serre graph is `A_{v₀}`, given by the empty path at `v₀`. -/
@[simp] theorem default_eq_mk_nil :
    (default : 𝔸.BassSerreVertex v₀) = mk (Quiver.Path.nil : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩) :=
  (rfl)

end BassSerreVertex

/-! ### Darts -/

namespace BassSerreDart

/-- The dart of the Bass–Serre graph over a dart `e` of `Γ` given by an `𝔸`-path `p` from `v₀`
to the source of `e`. -/
def mk (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) : 𝔸.BassSerreDart v₀ :=
  Quot.mk _ ⟨e, p⟩

variable {e : Γ.E}

/-- Two paths give the same dart over `e` exactly when `p ∼ q α_e(c)` for some `c ∈ A_e`. -/
theorem mk_eq_mk_iff {p q : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩} : mk e p = mk e q ↔
    ∃ c : 𝔸.edgeGroup (Γ.toGeomEdge e), p.Homotopic (q.cons (Letter.vertex (𝔸.α e c))) :=
  quot_mk_eq_quot_mk_iff.trans (by simp)

/-- Homotopic paths give the same dart. -/
theorem mk_eq_mk_of_homotopic {p q : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩} (h : p.Homotopic q) : mk e p = mk e q :=
  quot_mk_eq_quot_mk_of_homotopic h

/-- Appending an element of `α_e(A_e)` to a path does not change its dart over `e`. -/
@[simp] theorem mk_cons_α (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) (c : 𝔸.edgeGroup (Γ.toGeomEdge e)) :
    mk e (p.cons (Letter.vertex (𝔸.α e c))) = mk e p :=
  mk_eq_mk_iff.2 ⟨c, .refl _⟩

/-- The path given by an element `α_e(c)` of the vertex group at the source of `e` represents the
dart over `e` given by the empty path, `α_e(c) α_e(A_e) = α_e(A_e)`. -/
@[simp] theorem mk_ofVertex_α (c : 𝔸.edgeGroup (Γ.toGeomEdge e)) :
    mk e (Path.ofVertex (𝔸.α e c)) = mk e (Quiver.Path.nil : 𝔸.Path ⟨Γ.src e⟩ ⟨Γ.src e⟩) := by
  rw [Path.ofVertex_eq_nil_cons, mk_cons_α]

/-- Going along a dart and back does not change the dart over `e` given by a path. -/
@[simp] theorem mk_cons_dart_cons_dart_reverse {b : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩)
    (f : Γ.src e ⟶ b) :
    mk e ((p.cons (Letter.dart f)).cons (Letter.dart (Quiver.reverse f))) = mk e p :=
  mk_eq_mk_of_homotopic (.dart_reverse p f)

/-- Every dart of the Bass–Serre graph is given by a dart `e` of `Γ` and a path `p`. -/
@[elab_as_elim] theorem induction_on {P : 𝔸.BassSerreDart v₀ → Prop} (d : 𝔸.BassSerreDart v₀)
    (h : ∀ (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩), P (mk e p)) : P d :=
  Quot.ind (fun y ↦ h y.1 y.2) d

/-- A function `f` on darts `e` of `Γ` and `𝔸`-paths from `v₀` to the source of `e` descends to
the darts of the Bass–Serre graph when `f e p = f e q` whenever `p ∼ q α_e(c)` for some
`c ∈ A_e`, that is, when `f` is invariant under homotopy and under appending an element of
`α_e(A_e)` to the path. -/
def lift {β : Sort*} (f : ∀ e : Γ.E, 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩ → β)
    (hf : ∀ (e : Γ.E) (p q : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) (c : 𝔸.edgeGroup (Γ.toGeomEdge e)),
      p.Homotopic (q.cons (Letter.vertex (𝔸.α e c))) → f e p = f e q) : 𝔸.BassSerreDart v₀ → β :=
  Quot.lift (fun y ↦ f y.1 y.2) fun _ _ h ↦ by
    obtain ⟨p, q, _, ⟨c, rfl⟩, hpq⟩ := h
    exact hf _ p q c hpq

/-- `BassSerreDart.lift f hf` computes `f` on representatives. -/
@[simp] theorem lift_mk {β : Sort*} (f : ∀ e : Γ.E, 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩ → β)
    (hf : ∀ (e : Γ.E) (p q : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) (c : 𝔸.edgeGroup (Γ.toGeomEdge e)),
      p.Homotopic (q.cons (Letter.vertex (𝔸.α e c))) → f e p = f e q) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    lift f hf (mk e p) = f e p :=
  (rfl)

/-- The dart of `Γ` below a dart of the Bass–Serre graph. -/
def proj : 𝔸.BassSerreDart v₀ → Γ.E :=
  cosetIndex

/-- The dart over `e` given by `p` lies over `e`. -/
@[simp] theorem proj_mk (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) : (mk e p).proj = e :=
  (rfl)

/-- The dart over `e` given by `p` starts at the vertex `p A_{src e}`. -/
@[simp] theorem src_mk (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    (𝔸.bassSerreGraph v₀).src (mk e p) = BassSerreVertex.mk p :=
  (rfl)

/-- The source of a dart lies over the source of the dart of `Γ` below it. -/
@[simp] theorem proj_src (d : 𝔸.BassSerreDart v₀) :
    BassSerreVertex.proj ((𝔸.bassSerreGraph v₀).src d) = Γ.src d.proj :=
  induction_on d fun _ _ ↦ by simp

/-- The reverse of the dart over `e` given by `p` is the dart over `rev e` given by `p e`. -/
@[simp] theorem rev_mk (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    (𝔸.bassSerreGraph v₀).rev (mk e p) = mk (Γ.rev e) (p.cons (Letter.dart (Γ.dart e))) :=
  (rfl)

/-- The reverse of a dart lies over the reverse of the dart of `Γ` below it. -/
@[simp] theorem proj_rev (d : 𝔸.BassSerreDart v₀) :
    proj ((𝔸.bassSerreGraph v₀).rev d) = Γ.rev d.proj :=
  induction_on d fun _ _ ↦ by simp

-- The path `p e` is typed as ending at `src (rev e)`, as in `rev_mk`, so that the left-hand side
-- is the result of rewriting the reverse of the reverse of `mk e p` with `rev_mk`.
/-- Reversing twice the dart over `e` given by `p` gives it back, `p e (rev e) ∼ p`. -/
@[simp] theorem mk_rev_rev (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) : mk (Γ.rev (Γ.rev e))
    ((p.cons (Letter.dart (Γ.dart e)) : 𝔸.Path ⟨v₀⟩ ⟨Γ.src (Γ.rev e)⟩).cons
      (Letter.dart (Γ.dart (Γ.rev e)))) = mk e p := by
  simpa only [rev_mk] using (𝔸.bassSerreGraph v₀).rev_rev (mk e p)

-- The path `p e` is typed as ending at `src (rev e)`, as in `rev_mk`, so that the right-hand
-- side is also the source of the reverse of `mk e p` as computed by `rev_mk` and `src_mk`.
/-- The dart over `e` given by `p` ends at the vertex `p e A_{tgt e}`. -/
@[simp] theorem tgt_mk (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) : (𝔸.bassSerreGraph v₀).tgt (mk e p) =
    BassSerreVertex.mk (p.cons (Letter.dart (Γ.dart e)) : 𝔸.Path ⟨v₀⟩ ⟨Γ.src (Γ.rev e)⟩) := by
  rw [SerreGraph.tgt_def, rev_mk, src_mk]

/-- The target of a dart lies over the target of the dart of `Γ` below it. -/
@[simp] theorem proj_tgt (d : 𝔸.BassSerreDart v₀) :
    BassSerreVertex.proj ((𝔸.bassSerreGraph v₀).tgt d) = Γ.tgt d.proj := by
  simp only [SerreGraph.tgt_def, proj_src, proj_rev]

end BassSerreDart

-- The paths `p e` and `p e (rev e)` are typed as ending at `src (rev e)` and `src (rev (rev e))`,
-- as in `BassSerreDart.rev_mk` and `BassSerreDart.tgt_mk`, so that the left-hand side is the
-- target of the reverse of `BassSerreDart.mk e p` as computed by these two lemmas.
/-- Going along the dart `e` of `Γ` and back along `rev e` does not change the vertex,
`p e (rev e) A_{src e} = p A_{src e}`. -/
@[simp] theorem BassSerreVertex.mk_cons_dart_cons_dart_rev {e : Γ.E}
    (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) : BassSerreVertex.mk
      (((p.cons (Letter.dart (Γ.dart e)) : 𝔸.Path ⟨v₀⟩ ⟨Γ.src (Γ.rev e)⟩).cons
        (Letter.dart (Γ.dart (Γ.rev e)))) : 𝔸.Path ⟨v₀⟩ ⟨Γ.src (Γ.rev (Γ.rev e))⟩) =
      BassSerreVertex.mk p := by
  simpa only [BassSerreDart.src_mk] using
    congrArg (𝔸.bassSerreGraph v₀).src (BassSerreDart.mk_rev_rev p)

/-! ### The action of the fundamental group -/

variable (𝔸 v₀) in
/-- The action of `π₁(𝔸, v₀)` on its Bass–Serre graph by concatenation on the left,
`q · p A_a = q p A_a`, as a homomorphism to the automorphism group of the graph. -/
def bassSerreAction : π₁ 𝔸 v₀ →* (𝔸.bassSerreGraph v₀).Aut where
  toFun g :=
    -- `g` permutes the classes of paths that are the vertices and the darts. Instance search
    -- does not unfold `bassSerreGraph`, so the actions on these classes are passed explicitly.
    { equivV := @MulAction.toPerm _ _ _
        (inferInstanceAs (MulAction (π₁ 𝔸 v₀) (Quot (CosetRel 𝔸 (fun a ↦ a) (fun _ ↦ ⊤) v₀)))) g
      equivE := @MulAction.toPerm _ _ _ (inferInstanceAs
        (MulAction (π₁ 𝔸 v₀) (Quot (CosetRel 𝔸 Γ.src (fun e ↦ (𝔸.α e).range) v₀)))) g
      -- Source and reverse are computed on representatives, on which `q` acts by `p ↦ q p`:
      -- `src (q (e, p)) = q p A_{src e} = q src (e, p)` and `rev (q (e, p)) = q rev (e, p)`.
      map_src d := π₁.induction_on g fun q ↦ BassSerreDart.induction_on d fun _ p ↦
        (congrArg dartSrc (mk_smul_quot_mk q p)).trans
          (mk_smul_quot_mk (t := fun a ↦ a) (H := fun _ ↦ ⊤) q p).symm
      map_rev d := π₁.induction_on g fun q ↦ BassSerreDart.induction_on d fun _ p ↦
        (mk_smul_quot_mk q _).trans (congrArg dartRev (mk_smul_quot_mk q p)).symm }
  map_one' := by ext <;> simp
  map_mul' g h := by ext <;> simp [mul_smul]

/-- `π₁(𝔸, v₀)` acts on the vertices of the Bass–Serre graph through `bassSerreAction`: by
concatenation on the left, `q · p A_a = q p A_a`. -/
instance : MulAction (π₁ 𝔸 v₀) (𝔸.BassSerreVertex v₀) :=
  MulAction.compHom _ (𝔸.bassSerreAction v₀)

/-- `π₁(𝔸, v₀)` acts on the darts of the Bass–Serre graph through `bassSerreAction`: by
concatenation on the left. -/
instance : MulAction (π₁ 𝔸 v₀) (𝔸.BassSerreDart v₀) :=
  MulAction.compHom _ (𝔸.bassSerreAction v₀)

/-- The automorphism given by `g` acts on the vertices as `g` does. -/
@[simp] theorem bassSerreAction_smul_vertex (g : π₁ 𝔸 v₀) (y : 𝔸.BassSerreVertex v₀) :
    𝔸.bassSerreAction v₀ g • y = g • y :=
  (MulAction.compHom_smul_def _ g y).symm

/-- The automorphism given by `g` acts on the darts as `g` does. -/
@[simp] theorem bassSerreAction_smul_dart (g : π₁ 𝔸 v₀) (d : 𝔸.BassSerreDart v₀) :
    𝔸.bassSerreAction v₀ g • d = g • d :=
  (MulAction.compHom_smul_def _ g d).symm

/-- The automorphism given by `g` permutes the vertices as `g` does, `y ↦ g • y`. -/
@[simp] theorem bassSerreAction_equivV (g : π₁ 𝔸 v₀) :
    (𝔸.bassSerreAction v₀ g).equivV = MulAction.toPerm g :=
  Equiv.ext fun y ↦ by simp [← SerreGraph.Aut.smul_vertex_def]

/-- The automorphism given by `g` permutes the darts as `g` does, `d ↦ g • d`. -/
@[simp] theorem bassSerreAction_equivE (g : π₁ 𝔸 v₀) :
    (𝔸.bassSerreAction v₀ g).equivE = MulAction.toPerm g :=
  Equiv.ext fun d ↦ by simp [← SerreGraph.Aut.smul_dart_def]

/- By the definitions of `MulAction.compHom` and of `bassSerreAction`, an element `g` acts on a
vertex or a dart as it acts on classes of paths. So the results on classes of paths, about the
action of `π₁(𝔸, v₀)` on representatives, orbits and stabilizers, apply as they stand. -/

namespace BassSerreVertex

variable {a : Γ.V}

/-- A closed path `q` at `v₀` sends the vertex `p A_a` to `q p A_a`. -/
@[simp] theorem mk_smul_mk (q : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩) (p : 𝔸.Path ⟨v₀⟩ ⟨a⟩) :
    π₁.mk q • mk p = mk (q.comp p) :=
  mk_smul_quot_mk q _

/-- The action of `π₁(𝔸, v₀)` preserves the projection to `Γ`. -/
@[simp] theorem proj_smul (g : π₁ 𝔸 v₀) (y : 𝔸.BassSerreVertex v₀) : (g • y).proj = y.proj :=
  cosetIndex_smul g y

/-- Two vertices of the Bass–Serre graph lie in the same `π₁(𝔸, v₀)`-orbit exactly when they lie
over the same vertex of `Γ`. -/
theorem mem_orbit_iff_proj_eq {y z : 𝔸.BassSerreVertex v₀} :
    z ∈ orbit (π₁ 𝔸 v₀) y ↔ z.proj = y.proj :=
  mem_orbit_iff_cosetIndex

/-- The stabilizer of the vertex `p A_a` is `p A_a p⁻¹`, the image of `π₁.vertexHom p`. -/
theorem stabilizer_mk (p : 𝔸.Path ⟨v₀⟩ ⟨a⟩) :
    stabilizer (π₁ 𝔸 v₀) (mk p) = (π₁.vertexHom p).range :=
  (stabilizer_quot_mk _).trans (MonoidHom.range_eq_map _).symm

end BassSerreVertex

namespace BassSerreDart

variable {e : Γ.E}

/-- A closed path `q` at `v₀` sends the dart over `e` given by `p` to the one given by `q p`. -/
@[simp] theorem mk_smul_mk (q : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    π₁.mk q • mk e p = mk e (q.comp p) :=
  mk_smul_quot_mk q _

/-- The action of `π₁(𝔸, v₀)` preserves the projection to `Γ`. -/
@[simp] theorem proj_smul (g : π₁ 𝔸 v₀) (d : 𝔸.BassSerreDart v₀) : (g • d).proj = d.proj :=
  cosetIndex_smul g d

/-- The action of `π₁(𝔸, v₀)` commutes with taking sources. -/
@[simp] theorem src_smul (g : π₁ 𝔸 v₀) (d : 𝔸.BassSerreDart v₀) :
    (𝔸.bassSerreGraph v₀).src (g • d) = g • (𝔸.bassSerreGraph v₀).src d := by
  rw [← bassSerreAction_smul_dart, SerreGraph.Aut.src_smul, bassSerreAction_smul_vertex]

/-- The action of `π₁(𝔸, v₀)` commutes with reversal. -/
@[simp] theorem rev_smul (g : π₁ 𝔸 v₀) (d : 𝔸.BassSerreDart v₀) :
    (𝔸.bassSerreGraph v₀).rev (g • d) = g • (𝔸.bassSerreGraph v₀).rev d := by
  rw [← bassSerreAction_smul_dart, SerreGraph.Aut.rev_smul, bassSerreAction_smul_dart]

/-- The action of `π₁(𝔸, v₀)` commutes with taking targets. -/
@[simp] theorem tgt_smul (g : π₁ 𝔸 v₀) (d : 𝔸.BassSerreDart v₀) :
    (𝔸.bassSerreGraph v₀).tgt (g • d) = g • (𝔸.bassSerreGraph v₀).tgt d := by
  rw [← bassSerreAction_smul_dart, SerreGraph.Aut.tgt_smul, bassSerreAction_smul_vertex]

/-- The action of `π₁(𝔸, v₀)` on the Bass–Serre graph has no inversions: no element maps a dart
to its reverse. -/
theorem smul_ne_rev (g : π₁ 𝔸 v₀) (d : 𝔸.BassSerreDart v₀) :
    g • d ≠ (𝔸.bassSerreGraph v₀).rev d := fun h ↦
  Γ.rev_ne d.proj (by rw [← proj_rev, ← h, proj_smul])

/-- Two darts of the Bass–Serre graph lie in the same `π₁(𝔸, v₀)`-orbit exactly when they lie
over the same dart of `Γ`. -/
theorem mem_orbit_iff_proj_eq {d d' : 𝔸.BassSerreDart v₀} :
    d' ∈ orbit (π₁ 𝔸 v₀) d ↔ d'.proj = d.proj :=
  mem_orbit_iff_cosetIndex

/-- The stabilizer of the dart over `e` given by `p` is `p α_e(A_e) p⁻¹`. -/
theorem stabilizer_mk (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    stabilizer (π₁ 𝔸 v₀) (mk e p) = (𝔸.α e).range.map (π₁.vertexHom p) :=
  stabilizer_quot_mk _

/-- A dart and its reverse have the same stabilizer. -/
@[simp] theorem stabilizer_rev (d : 𝔸.BassSerreDart v₀) :
    stabilizer (π₁ 𝔸 v₀) ((𝔸.bassSerreGraph v₀).rev d) = stabilizer (π₁ 𝔸 v₀) d := by
  ext g
  rw [mem_stabilizer_iff, mem_stabilizer_iff, ← rev_smul,
    (𝔸.bassSerreGraph v₀).rev_injective.eq_iff]

end BassSerreDart

/-- The action of `π₁(𝔸, v₀)` on its Bass–Serre graph by automorphisms has no inversions. -/
theorem bassSerreAction_smul_ne_rev (g : π₁ 𝔸 v₀) (d : 𝔸.BassSerreDart v₀) :
    𝔸.bassSerreAction v₀ g • d ≠ (𝔸.bassSerreGraph v₀).rev d := by
  rw [bassSerreAction_smul_dart]
  exact BassSerreDart.smul_ne_rev g d

/-! ### The projection to the underlying graph -/

variable (𝔸 v₀) in
/-- The projection of the Bass–Serre graph to `Γ`: the vertex `p A_a` maps to `a`, and a dart over
a dart `e` of `Γ` maps to `e`. -/
def bassSerreProj : (𝔸.bassSerreGraph v₀).Hom Γ where
  mapV := BassSerreVertex.proj
  mapE := BassSerreDart.proj
  map_src d := (BassSerreDart.proj_src d).symm
  map_rev := BassSerreDart.proj_rev

/-- The projection sends a vertex to the vertex of `Γ` below it. -/
@[simp] theorem bassSerreProj_mapV (y : 𝔸.BassSerreVertex v₀) :
    (𝔸.bassSerreProj v₀).mapV y = y.proj :=
  (rfl)

/-- The projection sends a dart to the dart of `Γ` below it. -/
@[simp] theorem bassSerreProj_mapE (d : 𝔸.BassSerreDart v₀) :
    (𝔸.bassSerreProj v₀).mapE d = d.proj :=
  (rfl)

/-- The projection to `Γ` is invariant under the action of `π₁(𝔸, v₀)`. -/
@[simp] theorem bassSerreProj_comp_bassSerreAction_toHom (g : π₁ 𝔸 v₀) :
    SerreGraph.Hom.comp (𝔸.bassSerreProj v₀) (𝔸.bassSerreAction v₀ g).toHom =
      𝔸.bassSerreProj v₀ := by
  ext <;> simp

/-! ### Graphs without edges -/

section isEmpty

variable [IsEmpty Γ.E]

/-- Over a graph without edges, the Bass–Serre graph has exactly one vertex, the base vertex:
every `𝔸`-path from `v₀` ends at `v₀` and is homotopic to a single vertex group letter. -/
instance : Unique (𝔸.BassSerreVertex v₀) where
  toInhabited := inferInstance
  uniq y := y.induction_on fun a p ↦ by
    obtain rfl : v₀ = a := Γ.eq_of_path_of_forall_src_eq_tgt isEmptyElim (Path.edgePath p)
    obtain ⟨g, hg⟩ := π₁.exists_homotopic_ofVertex_of_isEmpty p
    rw [BassSerreVertex.default_eq_mk_nil, BassSerreVertex.mk_eq_mk_of_homotopic hg,
      BassSerreVertex.mk_ofVertex]

/-- Over a graph without edges, the Bass–Serre graph has no darts. -/
instance : IsEmpty (𝔸.BassSerreDart v₀) :=
  ⟨fun d ↦ isEmptyElim d.proj⟩

end isEmpty

end GraphOfGroups

end TauCeti
