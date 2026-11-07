/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Coset.Table

/-!
# Indexed checking of coset-table certificates

`CosetTable.checkFast` runs the same deductions as `CosetTable.check`, storing known
edges in array-backed Boolean vectors. Looking up a known edge no longer searches
the growing list of previous deductions. The certificate is folded once before
the final scan of all edges.

`CosetTable.checkFast_eq_check` proves equality of the two Boolean checks for every
table and certificate. In particular, the existing soundness and index bounds
apply without changing the relator, subgroup, tree-edge, or closure conditions.
This is a certificate-checking prerequisite for milestone P0 of
`TauCetiRoadmap/CFSGBasicProperties/README.md`.
-/

public section

namespace TauCeti.CosetTable

variable {m k : ℕ} (T : CosetTable m k)

/-- An indexed set of known edges, with one Boolean for each generator and point. -/
abbrev KnownEdges (m k : ℕ) := Vector (Vector Bool k) m

/-- The initial indexed state uses exactly the defining-word test of `treeEdges`. -/
@[expose]
def treeEdgesFast : KnownEdges m k :=
  Vector.ofFn fun t ↦ Vector.ofFn fun i ↦ decide (T.word (T.act t i) = t :: T.word i)

/-- One deduction with indexed edge lookups, using the same guard as `deduce`. -/
@[expose]
def deduceFast (known : KnownEdges m k) (i : Fin k) : List (Fin m) → KnownEdges m k
  | [] => known
  | t :: u =>
    if (T.edges u i).all (fun e ↦ known[e.1][e.2]) && T.act t (T.trace u i) = i then
      known.set t.val (known[t].set (T.trace u i).val true)
    else known

/-- The action check with indexed known edges. Certificate eligibility is unchanged. -/
@[expose]
def checkActionFast (rels stab : List (List (Fin m)))
    (cert : List (Fin k × List (Fin m))) : Bool :=
  cert.all (fun c ↦ c.2 ∈ rels || (T.word c.1 = [] && c.2 ∈ stab)) &&
    let known := cert.foldl (fun known c ↦ T.deduceFast known c.1 c.2) T.treeEdgesFast
    (List.finRange m).all fun t ↦ (List.finRange k).all fun i ↦ known[t][i]

/-- The indexed certificate check, including the existence of an empty-word point. -/
@[expose]
def checkFast (rels stab : List (List (Fin m))) (cert : List (Fin k × List (Fin m))) :
    Bool :=
  (List.finRange k).any (T.word · = []) && T.checkActionFast rels stab cert

private def Agrees (fast : KnownEdges m k) (known : List (Fin m × Fin k)) : Prop :=
  ∀ (t : Fin m) (i : Fin k), fast[t][i] = decide ((t, i) ∈ known)

private theorem agrees_treeEdges : Agrees T.treeEdgesFast T.treeEdges := by
  intro t i
  simp [treeEdgesFast, treeEdges]

private theorem agrees_set {fast : KnownEdges m k} {known : List (Fin m × Fin k)}
    (h : Agrees fast known) (t : Fin m) (i : Fin k) :
    Agrees (fast.set t.val (fast[t].set i.val true)) ((t, i) :: known) := by
  intro s j
  by_cases ht : t = s
  · subst s
    by_cases hi : i = j
    · subst j
      simp
    · have hij : i.val ≠ j.val := fun he ↦ hi (Fin.ext he)
      simpa [hij, Ne.symm hi] using h t j
  · have hts : t.val ≠ s.val := fun he ↦ ht (Fin.ext he)
    simpa [hts, Ne.symm ht] using h s j

private theorem agrees_deduce {fast : KnownEdges m k} {known : List (Fin m × Fin k)}
    (h : Agrees fast known) (i : Fin k) (r : List (Fin m)) :
    Agrees (T.deduceFast fast i r) (T.deduce known i r) := by
  cases r with
  | nil => exact h
  | cons t u =>
    have he : (T.edges u i).all (fun e ↦ fast[e.1][e.2]) =
        (T.edges u i).all (fun e ↦ decide (e ∈ known)) := by
      congr 1
      funext e
      exact h e.1 e.2
    simp only [deduceFast, deduce, he]
    split_ifs
    · exact agrees_set h t (T.trace u i)
    · exact h

private theorem agrees_foldl {fast : KnownEdges m k} {known : List (Fin m × Fin k)}
    (h : Agrees fast known) (cert : List (Fin k × List (Fin m))) :
    Agrees (cert.foldl (fun state c ↦ T.deduceFast state c.1 c.2) fast)
      (cert.foldl (fun state c ↦ T.deduce state c.1 c.2) known) := by
  induction cert generalizing fast known with
  | nil => exact h
  | cons c cert ih =>
    exact ih (T.agrees_deduce h c.1 c.2)

/-- Indexed and list-based action checks agree for every deduction certificate. -/
theorem checkActionFast_eq_checkAction (rels stab : List (List (Fin m)))
    (cert : List (Fin k × List (Fin m))) :
    T.checkActionFast rels stab cert = T.checkAction rels stab cert := by
  dsimp only [checkActionFast, checkAction]
  have h := T.agrees_foldl T.agrees_treeEdges cert
  congr 1
  congr 1
  funext t
  congr 1
  funext i
  exact h t i

/-- The fast check accepts exactly the certificates accepted by the original check. -/
theorem checkFast_eq_check (rels stab : List (List (Fin m)))
    (cert : List (Fin k × List (Fin m))) :
    T.checkFast rels stab cert = T.check rels stab cert := by
  rw [checkFast, check, checkActionFast_eq_checkAction]

end TauCeti.CosetTable
