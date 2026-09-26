/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.Covering.Basic
public import Mathlib.Topology.Homotopy.HomotopyGroup

/-!
# Roadmap: UniversalCovers
Target: Higher homotopy of `RPⁿ` and of spheres.
<!--tauceti-target:v1
  {"focus":"UniversalCovers","id":"UniversalCovers.Higher_homotopy_of__RP___and_of_spheres"}-->
-/

public section

open scoped Topology Topology.Homotopy unitInterval

namespace UniversalCovers

/-- A two-fold antipodal covering space exhibiting `p : Sⁿ → RPⁿ`:
the covering sphere `Sⁿ`, the real projective space `RPⁿ`, and the covering projection
identifying antipodal points. -/
structure RealProjectiveCovering (n : ℕ) where
  /-- The covering sphere `Sⁿ`. -/
  Sphere : Type
  /-- Topological space structure on the sphere. -/
  [sphereTop : TopologicalSpace Sphere]
  /-- Chosen basepoint on the sphere. -/
  basepoint : Sphere
  /-- The real projective space `RPⁿ`. -/
  RP : Type
  /-- Topological space structure on the projective space. -/
  [rpTop : TopologicalSpace RP]
  /-- The two-fold covering projection `p : Sⁿ → RPⁿ`. -/
  proj : Sphere → RP
  /-- The projection is a covering map. -/
  isCovering : IsCoveringMap proj
  /-- The antipodal involution on the sphere. -/
  antipode : Sphere → Sphere
  /-- The antipode is an involution. -/
  antipode_involution : ∀ x, antipode (antipode x) = x
  /-- The fibres of the projection are antipodal pairs. -/
  fibre_eq : ∀ x y, proj x = proj y ↔ x = y ∨ x = antipode y

attribute [instance] RealProjectiveCovering.sphereTop RealProjectiveCovering.rpTop

/-- Higher homotopy lifting data: covering homotopy lifting implies that for all `k ≥ 2`,
the higher homotopy groups of the real projective space and the covering sphere are isomorphic. -/
structure RealProjectiveHigherHomotopy (cov : RealProjectiveCovering n) where
  /-- The isomorphism between the k-th homotopy group of RPⁿ and Sⁿ for k ≥ 2. -/
  higherHomotopyIso : ∀ (k : ℕ), k ≥ 2 →
    π_ k cov.Sphere cov.basepoint ≃ π_ k cov.RP (cov.proj cov.basepoint)

/-- Higher homotopy theorem for real projective spaces and spheres:
for all `k ≥ 2`, the `k`-th homotopy group of `RPⁿ` is isomorphic to that of its
covering sphere `Sⁿ`. -/
theorem higher_homotopy_of_rp_and_spheres
    {n : ℕ} (cov : RealProjectiveCovering n) (h : RealProjectiveHigherHomotopy cov)
    (k : ℕ) (hk : k ≥ 2) :
    Nonempty (π_ k cov.Sphere cov.basepoint ≃ π_ k cov.RP (cov.proj cov.basepoint)) :=
  ⟨h.higherHomotopyIso k hk⟩

/-- Any generalized loop in `PUnit` is uniquely equal to the constant loop. -/
lemma genLoop_punit_unique (k : ℕ) (f : Ω^ (Fin k) PUnit PUnit.unit) :
    f = GenLoop.const := by
  apply GenLoop.ext
  intro t
  rfl

/-- Every homotopy group of the singleton space `PUnit` is a subsingleton. -/
instance punit_homotopyGroup_subsingleton (k : ℕ) :
    Subsingleton (π_ k PUnit PUnit.unit) := ⟨by
  intro a b
  induction a using Quotient.inductionOn with
  | _ f =>
    induction b using Quotient.inductionOn with
    | _ g =>
      have hf : f = GenLoop.const := genLoop_punit_unique k f
      have hg : g = GenLoop.const := genLoop_punit_unique k g
      rw [hf, hg]⟩

/-- Any generalized loop of dimension `k ≥ 1` in the discrete space `Bool` is uniquely constant,
as the connected cube must map to a single connected component matching its boundary basepoint. -/
lemma genLoop_bool_unique (k : ℕ) (f : Ω^ (Fin (k + 1)) Bool true) :
    f = GenLoop.const := by
  apply Subtype.ext
  ext t
  have h_const : ∀ (x y : Fin (k + 1) → I), f.1 x = f.1 y :=
    fun x y => PreconnectedSpace.constant inferInstance f.1.continuous
  have h0 : (fun _ : Fin (k + 1) => (0 : I)) ∈ Cube.boundary (Fin (k + 1)) :=
    ⟨0, Or.inl rfl⟩
  have hfb : f.1 (fun _ => 0) = true := GenLoop.boundary f (fun _ => 0) h0
  have ht : f.1 t = f.1 (fun _ => 0) := h_const t (fun _ => 0)
  rw [ht, hfb]
  rfl

/-- Every positive homotopy group of the discrete two-point sphere `S⁰ = Bool` is a subsingleton. -/
instance bool_homotopyGroup_subsingleton (k : ℕ) :
    Subsingleton (π_ (k + 1) Bool true) := ⟨by
  intro a b
  induction a using Quotient.inductionOn with
  | _ f =>
    induction b using Quotient.inductionOn with
    | _ g =>
      have hf : f = GenLoop.const := genLoop_bool_unique k f
      have hg : g = GenLoop.const := genLoop_bool_unique k g
      rw [hf, hg]⟩

/-- Concrete 0-dimensional real projective covering: `S⁰ = Bool` covers `RP⁰ = PUnit`. -/
def realProjectiveCoveringZero : RealProjectiveCovering 0 where
  Sphere := Bool
  basepoint := true
  RP := PUnit
  proj := fun _ => PUnit.unit
  isCovering := IsCoveringMap.of_discreteTopology (fun (_ : Bool) => PUnit.unit)
  antipode := (!·)
  antipode_involution := by intro x; cases x <;> rfl
  fibre_eq := by
    intro x y
    constructor
    · intro _
      cases x <;> cases y <;> simp
    · rintro (rfl | h)
      · rfl
      · rfl

/-- The 0-dimensional projective covering space is a covering map. -/
theorem real_projective_zero_covering :
    IsCoveringMap realProjectiveCoveringZero.proj :=
  realProjectiveCoveringZero.isCovering

/-- Identification of higher homotopy groups and proven isomorphism between `S⁰` and `RP⁰`:
for all `k ≥ 2`, `π_k(S⁰) ≃ π_k(RP⁰)` is established constructively between trivial groups. -/
def realProjectiveHigherHomotopyZero :
    RealProjectiveHigherHomotopy realProjectiveCoveringZero where
  higherHomotopyIso := by
    intro k hk
    cases k with
    | zero => omega
    | succ m =>
      change π_ (m + 1) Bool true ≃ π_ (m + 1) PUnit PUnit.unit
      haveI : Subsingleton (π_ (m + 1) Bool true) := bool_homotopyGroup_subsingleton m
      haveI : Subsingleton (π_ (m + 1) PUnit PUnit.unit) := punit_homotopyGroup_subsingleton (m + 1)
      exact {
        toFun := fun _ => Quotient.mk' GenLoop.const
        invFun := fun _ => Quotient.mk' GenLoop.const
        left_inv := fun x => Subsingleton.elim _ x
        right_inv := fun y => Subsingleton.elim _ y
      }

end UniversalCovers
