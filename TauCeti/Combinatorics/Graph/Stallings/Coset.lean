/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Stallings.Core
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# The based coset graph of a free-group subgroup

The coset graph of a subgroup has a vertex for each left coset and one outgoing dart
for each signed basis letter. Its based core is a folded labelled graph accepting exactly
that subgroup. This construction supplies the existence side of the Stallings correspondence,
including for subgroups that are not finitely generated.

## References

* I. Kapovich and A. Myasnikov, *Stallings foldings and subgroups of free groups*,
  Section 5, Theorem 5.1.
* Mathlib's `Quiver.SchreierGraph` gives the corresponding directed action graph;
  here signed letters and edge reversal present it as a Serre graph.
-/

public section

namespace Subgroup

open TauCeti

variable {G : Type*} [Group G] (K : Subgroup G)

/-- Following a word on left cosets uses the inverse left action, so successive
letters act in the same order as group multiplication. -/
def cosetStep (q : G ⧸ K) (g : G) : G ⧸ K :=
  g⁻¹ • q

@[simp]
theorem cosetStep_one (q : G ⧸ K) : cosetStep K q 1 = q := by
  simp [cosetStep]

theorem cosetStep_mul (q : G ⧸ K) (g h : G) :
    cosetStep K (cosetStep K q g) h = cosetStep K q (g * h) := by
  simp [cosetStep, mul_smul, mul_inv_rev]

/-- The elements returning the distinguished left coset to itself are precisely the subgroup. -/
theorem cosetStep_one_eq_iff (g : G) :
    cosetStep K (QuotientGroup.mk 1) g = (QuotientGroup.mk 1 : G ⧸ K) ↔ g ∈ K := by
  simp only [cosetStep, MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]
  rw [QuotientGroup.eq]
  simp

variable {α : Type*} (H : Subgroup (FreeGroup α))

/-- The Serre graph of left cosets of a subgroup. A signed letter `l` leaves `q`
and arrives at `(mk [l])⁻¹ • q`. -/
abbrev cosetGraph (H : Subgroup (FreeGroup α)) : StallingsGraph α where
  graph := {
    V := FreeGroup α ⧸ H
    E := (FreeGroup α ⧸ H) × (α × Bool)
    src := Prod.fst
    rev := fun e => (cosetStep H e.1 (FreeGroup.mk [e.2]), (e.2.1, !e.2.2))
    rev_rev := by
      rintro ⟨q, a, b⟩
      apply Prod.ext
      · have h : FreeGroup.mk [(a, !b)] = (FreeGroup.mk [(a, b)])⁻¹ := by
          cases b <;> simp [FreeGroup.inv_mk, FreeGroup.invRev]
        simp only [cosetStep_mul, h, mul_inv_cancel, cosetStep_one]
      · cases b <;> rfl
    rev_ne := by
      intro e h
      have h' := congrArg (fun x : (FreeGroup α ⧸ H) × (α × Bool) => x.2.2) h
      cases e.2.2 <;> simp at h' }
  base := QuotientGroup.mk 1
  label := Prod.snd
  label_rev := by intro e; rfl

/-- The quiver induced by the coset Serre graph, used for paths in this file. -/
@[instance_reducible] local instance cosetGraphQuiver :
    Quiver (cosetGraph H).graph.V := (cosetGraph H).graph.toQuiver

/-- Reversal of darts in the quiver of the coset Serre graph. -/
@[instance_reducible] local instance cosetGraphReverse :
    Quiver.HasInvolutiveReverse (cosetGraph H).graph.V :=
  (cosetGraph H).graph.toQuiverHasInvolutiveReverse

@[simp] theorem cosetGraph_base : (cosetGraph H).base = QuotientGroup.mk 1 := rfl

@[simp] theorem cosetGraph_label (e : (cosetGraph H).graph.E) :
    (cosetGraph H).label e = e.2 := rfl

@[simp] theorem cosetGraph_src (e : (cosetGraph H).graph.E) :
    (cosetGraph H).graph.src e = e.1 := rfl

@[simp] theorem cosetGraph_tgt (e : (cosetGraph H).graph.E) :
    (cosetGraph H).graph.tgt e = cosetStep H e.1 (FreeGroup.mk [e.2]) := by
  rw [SerreGraph.tgt_def]

/-- The coset graph is folded: each signed letter has one outgoing dart. -/
theorem cosetGraph_isFolded : (cosetGraph H).IsFolded := by
  apply (cosetGraph H).isFolded_def.mpr
  intro e f hs hl
  exact Prod.ext hs hl

/-- A path in the coset graph ends at the coset obtained by following its reading. -/
theorem cosetGraph_path_endpoint {q r : (cosetGraph H).graph.V}
    (p : (cosetGraph H).graph.Path q r) :
    r = cosetStep H q ((cosetGraph H).read p) := by
  induction p with
  | nil =>
      rw [(cosetGraph H).read_nil]
      exact (cosetStep_one H q).symm
  | @cons b c p e ih =>
      rw [(cosetGraph H).read_cons, cosetGraph_label, ← cosetStep_mul, ← ih]
      have hs : e.1.1 = b := e.2.1
      simpa only [hs] using e.2.2.symm.trans (cosetGraph_tgt H e.1)

/-- A free-group word labels a path from any coset to the coset reached by the word. -/
theorem cosetGraph_exists_path_read (q : FreeGroup α ⧸ H) (g : FreeGroup α) :
    ∃ p : (cosetGraph H).graph.Path q (cosetStep H q g),
      (cosetGraph H).read p = g := by
  induction g using FreeGroup.induction_on generalizing q with
  | one =>
      rw [cosetStep_one]
      exact ⟨.nil, (cosetGraph H).read_nil q⟩
  | of a =>
      have he : (cosetGraph H).graph.tgt (q, (a, true)) =
          cosetStep H q (FreeGroup.of a) := by
        simpa only [FreeGroup.of] using cosetGraph_tgt H (q, (a, true))
      let e : Quiver.Hom q (cosetStep H q (FreeGroup.of a)) :=
        ⟨(q, (a, true)), rfl, he⟩
      refine ⟨e.toPath, ?_⟩
      simp only [(cosetGraph H).read_toPath, e, FreeGroup.of]
  | inv_of a _ =>
      have he : (cosetGraph H).graph.tgt (q, (a, false)) =
          cosetStep H q (FreeGroup.of a)⁻¹ := by
        rw [cosetGraph_tgt]
        simp [FreeGroup.of, FreeGroup.inv_mk, FreeGroup.invRev]
      let e : Quiver.Hom q (cosetStep H q (FreeGroup.of a)⁻¹) :=
        ⟨(q, (a, false)), rfl, he⟩
      refine ⟨e.toPath, ?_⟩
      simp only [(cosetGraph H).read_toPath, e]
      simp [FreeGroup.of, FreeGroup.inv_mk, FreeGroup.invRev]
  | mul g h ihg ihh =>
      obtain ⟨p, hp⟩ := ihg q
      obtain ⟨r, hr⟩ := ihh (cosetStep H q g)
      rw [← cosetStep_mul]
      refine ⟨p.comp r, ?_⟩
      rw [(cosetGraph H).read_comp, hp, hr]

/-- The loops at the base coset read exactly the original subgroup. -/
@[simp] theorem cosetGraph_subgroup :
    (cosetGraph H).subgroup (cosetGraph H).base = H := by
  ext g
  constructor
  · intro hg
    obtain ⟨p, hp⟩ := (cosetGraph H).mem_subgroup_iff.mp hg
    have h := cosetGraph_path_endpoint H p
    rw [hp] at h
    exact (cosetStep_one_eq_iff H g).mp h.symm
  · intro hg
    obtain ⟨p, hp⟩ := cosetGraph_exists_path_read H (cosetGraph H).base g
    have h := (cosetStep_one_eq_iff H g).mpr hg
    apply (cosetGraph H).mem_subgroup_iff.mpr
    exact Eq.mp (congrArg (fun x =>
      ∃ p : (cosetGraph H).graph.Path (cosetGraph H).base x,
        (cosetGraph H).read p = g) h) ⟨p, hp⟩

/-- Every coset is reachable from the distinguished coset. -/
theorem cosetGraph_base_reachable (q : (cosetGraph H).graph.V) :
    Nonempty ((cosetGraph H).graph.Path (cosetGraph H).base q) := by
  induction q using QuotientGroup.induction_on with
  | H x =>
      have h : cosetStep H (cosetGraph H).base x⁻¹ =
          (QuotientGroup.mk x : FreeGroup α ⧸ H) := by
        simp [cosetStep, MulAction.Quotient.smul_mk, smul_eq_mul]
      obtain ⟨p, _⟩ := cosetGraph_exists_path_read H (cosetGraph H).base x⁻¹
      exact ⟨h ▸ p⟩

/-- The coset graph is connected, even when the subgroup has infinite index. -/
theorem cosetGraph_connected : (cosetGraph H).graph.Connected := by
  apply (cosetGraph H).graph.connected_iff.mpr
  refine ⟨⟨(cosetGraph H).base⟩, ?_⟩
  rw [(cosetGraph H).graph.preconnected_iff]
  intro q r
  obtain ⟨p⟩ := cosetGraph_base_reachable H q
  obtain ⟨s⟩ := cosetGraph_base_reachable H r
  exact ⟨p.reverse.comp s⟩

/-- The based core of the coset graph is the canonical connected folded core
representing a subgroup. -/
def subgroupGraph (H : Subgroup (FreeGroup α)) : StallingsGraph α :=
  (cosetGraph H).core

/-- The subgroup graph is the based core of the coset graph. -/
theorem subgroupGraph_def : subgroupGraph H = (cosetGraph H).core := (rfl)

/-- The based core of the coset graph reads precisely the given subgroup. -/
@[simp] theorem subgroupGraph_subgroup :
    (subgroupGraph H).subgroup (subgroupGraph H).base = H := by
  exact ((cosetGraph H).core_subgroup).trans (cosetGraph_subgroup H)

/-- The canonical subgroup graph is folded. -/
theorem subgroupGraph_isFolded : (subgroupGraph H).IsFolded :=
  (cosetGraph_isFolded H).core

/-- The canonical subgroup graph is a based core, hence connected. -/
theorem subgroupGraph_isCore :
    (subgroupGraph H).graph.IsCore (subgroupGraph H).base :=
  (cosetGraph H).core_isCore

/-- The canonical subgroup graph is connected, including when the subgroup is trivial. -/
theorem subgroupGraph_connected : (subgroupGraph H).graph.Connected := by
  exact (subgroupGraph_isCore H).connected

end Subgroup
