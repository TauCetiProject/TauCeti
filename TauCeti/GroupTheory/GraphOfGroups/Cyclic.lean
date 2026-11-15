/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GraphOfGroups.OneEdge
public import TauCeti.GroupTheory.PresentedGroup
public import Mathlib.Algebra.Group.Torsion
public import Mathlib.Data.Int.Cast.Lemmas

/-!
# One-edge graphs of infinite cyclic groups

The two one-edge graphs of groups all of whose vertex and edge groups are infinite cyclic, with
their fundamental groups as two-generator one-relator groups. The group `ℤ` is written
multiplicatively, as `Multiplicative ℤ`, with generator `a = Multiplicative.ofAdd 1`, and
multiplication by a nonzero integer `m` is the monomorphism `c ↦ c ^ m`.

* The loop `GraphOfGroups.baumslagSolitar m n hm hn` has boundary maps `α = (· ^ m)` and
  `ω = (· ^ n)` on its dart `e = ((), true)`. The defining relation `e ω_e(c) e⁻¹ = α_e(c)` makes
  its fundamental group, relative to the empty maximal tree, the Baumslag–Solitar group
  `⟨a, t ∣ t a ^ n t⁻¹ = a ^ m⟩`, with `t` the dart `e`. For `m = 1` and `n = 2` this is
  `BS(1, 2) = ⟨a, t ∣ t a² t⁻¹ = a⟩`.
* The segment `GraphOfGroups.cyclicAmalgam m n hm hn` has boundary maps `(· ^ m)` and `(· ^ n)`
  into its two vertex groups. Its fundamental group, relative to its maximal tree, is the
  amalgam `ℤ ∗_ℤ ℤ = ⟨x, y ∣ x ^ m = y ^ n⟩`. For `m = 2` and `n = 3` this is the trefoil knot
  group `⟨x, y ∣ x² = y³⟩`.

The generators of the presented groups are indexed by `Bool`: `false` is `a`, respectively `x`,
and `true` is `t`, respectively `y`.

## Main definitions

* `TauCeti.GraphOfGroups.baumslagSolitar`: the loop of infinite cyclic groups.
* `TauCeti.GraphOfGroups.baumslagSolitarRelator`: the relator `t a ^ n t⁻¹ a ^ (-m)`.
* `TauCeti.GraphOfGroups.π₁Tree.baumslagSolitarEquiv`: the fundamental group of the loop is
  `⟨a, t ∣ t a ^ n t⁻¹ = a ^ m⟩`.
* `TauCeti.GraphOfGroups.cyclicAmalgam`: the segment of infinite cyclic groups.
* `TauCeti.GraphOfGroups.cyclicAmalgamRelator`: the relator `x ^ m y ^ (-n)`.
* `TauCeti.GraphOfGroups.π₁Tree.cyclicAmalgamEquiv`: the fundamental group of the segment is
  `⟨x, y ∣ x ^ m = y ^ n⟩`.

## References

* J.-P. Serre, *Trees*, Chapter I, §1.1 and §5.1.
* I. Kapovich, R. Weidmann, A. Myasnikov, *Foldings, graphs of groups and the membership problem*,
  Internat. J. Algebra Comput. 15 (2005), §2, Convention 2.1.
* G. Baumslag, D. Solitar, *Some two-generator one-relator non-Hopfian groups*,
  Bull. Amer. Math. Soc. 68 (1962).
-/

public section

namespace TauCeti

namespace GraphOfGroups

open Multiplicative

variable (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)

/-! ### The loop: Baumslag–Solitar groups -/

/-- The loop of infinite cyclic groups: one vertex and one loop, with vertex and edge group `ℤ`,
whose dart `((), true)` has boundary monomorphisms `α = (· ^ m)` and `ω = (· ^ n)`. Its
fundamental group is the Baumslag–Solitar group `⟨a, t ∣ t a ^ n t⁻¹ = a ^ m⟩`. -/
@[expose] def baumslagSolitar : GraphOfGroups.{0, 0, 0, 0} (SerreGraph.rose Unit) :=
  loop (zpowGroupHom (α := Multiplicative ℤ) m) (zpowGroupHom n) (zpow_left_injective hm)
    (zpow_left_injective hn)

@[simp] theorem baumslagSolitar_ω_true :
    (baumslagSolitar m n hm hn).ω ((), true) = zpowGroupHom (α := Multiplicative ℤ) n := (rfl)

@[simp] theorem baumslagSolitar_ω_false :
    (baumslagSolitar m n hm hn).ω ((), false) = zpowGroupHom (α := Multiplicative ℤ) m := (rfl)

@[simp] theorem baumslagSolitar_α_true :
    (baumslagSolitar m n hm hn).α ((), true) = zpowGroupHom (α := Multiplicative ℤ) m :=
  loop_α_true ..

@[simp] theorem baumslagSolitar_α_false :
    (baumslagSolitar m n hm hn).α ((), false) = zpowGroupHom (α := Multiplicative ℤ) n :=
  loop_α_false ..

/-- The Baumslag–Solitar relator `t a ^ n t⁻¹ a ^ (-m)` in the free group on `a = false` and
`t = true`. -/
def baumslagSolitarRelator : FreeGroup Bool :=
  FreeGroup.of true * FreeGroup.of false ^ n * (FreeGroup.of true)⁻¹ * (FreeGroup.of false ^ m)⁻¹

@[simp] theorem lift_baumslagSolitarRelator {H : Type*} [Group H] (f : Bool → H) :
    FreeGroup.lift f (baumslagSolitarRelator m n) =
      f true * f false ^ n * (f true)⁻¹ * (f false ^ m)⁻¹ := by
  simp [baumslagSolitarRelator]

/-- The defining relation `t a ^ n t⁻¹ = a ^ m` of the Baumslag–Solitar group. -/
theorem baumslagSolitarRelator_relation :
    (PresentedGroup.of true * PresentedGroup.of false ^ n * (PresentedGroup.of true)⁻¹ :
      PresentedGroup {baumslagSolitarRelator m n}) = PresentedGroup.of false ^ m := by
  have h := PresentedGroup.one_of_mem (rels := {baumslagSolitarRelator m n}) rfl
  rw [← PresentedGroup.lift_of_eq_mk, lift_baumslagSolitarRelator] at h
  exact mul_inv_eq_one.1 h

/-- The defining relation of the Baumslag–Solitar group on all powers of `a`: conjugation by `t`
carries the image of `c ^ n` to the image of `c ^ m`, for every `c` in the infinite cyclic
group. -/
private theorem of_true_mul_zpowersHom_zpow_mul_inv (c : Multiplicative ℤ) :
    (PresentedGroup.of true * zpowersHom _ (PresentedGroup.of false) (c ^ n) *
      (PresentedGroup.of true)⁻¹ : PresentedGroup {baumslagSolitarRelator m n}) =
      zpowersHom _ (PresentedGroup.of false) (c ^ m) := by
  have h := congrArg (· ^ c.toAdd) (baumslagSolitarRelator_relation m n)
  simp only [conj_zpow] at h
  simpa only [map_zpow, zpowersHom_apply, ← zpow_mul, mul_comm c.toAdd] using h

/-- The inverse form of the defining relation: conjugation by `t⁻¹` carries the image of `c ^ m`
to the image of `c ^ n`. -/
private theorem of_true_inv_mul_zpowersHom_zpow_mul (c : Multiplicative ℤ) :
    ((PresentedGroup.of true)⁻¹ * zpowersHom _ (PresentedGroup.of false) (c ^ m) *
      (PresentedGroup.of true)⁻¹⁻¹ : PresentedGroup {baumslagSolitarRelator m n}) =
      zpowersHom _ (PresentedGroup.of false) (c ^ n) := by
  rw [← of_true_mul_zpowersHom_zpow_mul_inv]
  simp [mul_assoc]

namespace π₁Tree

/-- The defining relation `e c ^ n e⁻¹ = c ^ m` of the dart `e = ((), true)` of the loop of
infinite cyclic groups. -/
theorem baumslagSolitar_edge_mul_of_zpow_mul_edge_inv (c : Multiplicative ℤ) :
    edge ∅ ((), true) * of (𝔸 := baumslagSolitar m n hm hn) ∅ () (c ^ n) *
        (edge ∅ ((), true))⁻¹ = of (𝔸 := baumslagSolitar m n hm hn) ∅ () (c ^ m) := by
  have h := edge_mul_of_ω_mul_edge_inv (𝔸 := baumslagSolitar m n hm hn) (T := ∅) ((), true) c
  rw [baumslagSolitar_ω_true, baumslagSolitar_α_true] at h
  -- The vertices `tgt ((), true)` and `src ((), true)` are `()`, and `zpowGroupHom n c` is
  -- `c ^ n`, by definition.
  exact h

/-- The map from the fundamental group of the loop of infinite cyclic groups to the
Baumslag–Solitar group: the generator of the vertex group maps to `a` and the dart `((), true)`
to `t`. -/
private noncomputable def toBaumslagSolitar :
    π₁Tree (baumslagSolitar m n hm hn) ∅ →* PresentedGroup {baumslagSolitarRelator m n} :=
  lift (fun _ => zpowersHom _ (PresentedGroup.of false))
    (fun e => cond e.2 (PresentedGroup.of true) (PresentedGroup.of true)⁻¹)
    (fun _ h => h.elim)
    (fun e => by
      obtain ⟨⟨⟩, _ | _⟩ := e <;> simp)
    -- The edge group of every dart of the loop is `Multiplicative ℤ` by definition.
    (fun e (c : Multiplicative ℤ) => by
      obtain ⟨⟨⟩, _ | _⟩ := e
      · simp only [baumslagSolitar_ω_false, baumslagSolitar_α_false]
        exact of_true_inv_mul_zpowersHom_zpow_mul m n c
      · simp only [baumslagSolitar_ω_true, baumslagSolitar_α_true]
        exact of_true_mul_zpowersHom_zpow_mul_inv m n c)

private theorem toBaumslagSolitar_of (c : Multiplicative ℤ) :
    toBaumslagSolitar m n hm hn (of ∅ () c) = PresentedGroup.of false ^ c.toAdd :=
  (lift_of (𝔸 := baumslagSolitar m n hm hn) (T := ∅) _ _ _ _ _ () c).trans (zpowersHom_apply ..)

private theorem toBaumslagSolitar_edge_true :
    toBaumslagSolitar m n hm hn (edge ∅ ((), true)) = PresentedGroup.of true :=
  lift_edge (𝔸 := baumslagSolitar m n hm hn) (T := ∅) _ _ _ _ _ ((), true)

private theorem toBaumslagSolitar_edge_false :
    toBaumslagSolitar m n hm hn (edge ∅ ((), false)) = (PresentedGroup.of true)⁻¹ :=
  lift_edge (𝔸 := baumslagSolitar m n hm hn) (T := ∅) _ _ _ _ _ ((), false)

/-- The inverse map from the Baumslag–Solitar group to the fundamental group of the loop of
infinite cyclic groups, sending `a` to the generator of the vertex group and `t` to the dart
`((), true)`. -/
private noncomputable def ofBaumslagSolitar :
    PresentedGroup {baumslagSolitarRelator m n} →* π₁Tree (baumslagSolitar m n hm hn) ∅ :=
  PresentedGroup.toGroup
    (f := fun b => cond b (edge ∅ ((), true))
      (of (𝔸 := baumslagSolitar m n hm hn) ∅ () (ofAdd (1 : ℤ))))
    (by
      rintro _ rfl
      rw [lift_baumslagSolitarRelator, mul_inv_eq_one]
      -- Powers of the generator are moved into `of`, whose source is `Multiplicative ℤ` only
      -- by definition.
      exact (congrArg (fun x => edge ∅ ((), true) * x * (edge ∅ ((), true))⁻¹)
        (map_zpow (of (𝔸 := baumslagSolitar m n hm hn) ∅ ()) (ofAdd (1 : ℤ)) n).symm).trans
        ((baumslagSolitar_edge_mul_of_zpow_mul_edge_inv m n hm hn (ofAdd 1)).trans
          (map_zpow (of (𝔸 := baumslagSolitar m n hm hn) ∅ ()) (ofAdd (1 : ℤ)) m)))

private theorem ofBaumslagSolitar_of_false :
    ofBaumslagSolitar m n hm hn (PresentedGroup.of false) = of ∅ () (ofAdd (1 : ℤ)) :=
  PresentedGroup.toGroup.of _

private theorem ofBaumslagSolitar_of_true :
    ofBaumslagSolitar m n hm hn (PresentedGroup.of true) = edge ∅ ((), true) :=
  PresentedGroup.toGroup.of _

/-- The fundamental group of the loop of infinite cyclic groups with `α = (· ^ m)` and
`ω = (· ^ n)`, relative to its maximal tree `∅`, is the Baumslag–Solitar group
`⟨a, t ∣ t a ^ n t⁻¹ = a ^ m⟩`: the generator of the vertex group corresponds to `a` and the dart
`((), true)` to `t`. -/
noncomputable def baumslagSolitarEquiv :
    π₁Tree (baumslagSolitar m n hm hn) ∅ ≃* PresentedGroup {baumslagSolitarRelator m n} :=
  MonoidHom.toMulEquiv (toBaumslagSolitar m n hm hn) (ofBaumslagSolitar m n hm hn)
    (hom_ext (fun ⟨⟩ => MonoidHom.ext_mint <|
        (congrArg (ofBaumslagSolitar m n hm hn) (toBaumslagSolitar_of m n hm hn (ofAdd 1))).trans
          ((congrArg _ (by simp)).trans (ofBaumslagSolitar_of_false m n hm hn)))
      fun e => by
        obtain ⟨⟨⟩, _ | _⟩ := e
        · refine (congrArg (ofBaumslagSolitar m n hm hn)
            (toBaumslagSolitar_edge_false m n hm hn)).trans ?_
          rw [map_inv, ofBaumslagSolitar_of_true]
          exact (edge_rev (𝔸 := baumslagSolitar m n hm hn) (T := ∅) ((), true)).symm
        · exact (congrArg (ofBaumslagSolitar m n hm hn)
            (toBaumslagSolitar_edge_true m n hm hn)).trans (ofBaumslagSolitar_of_true m n hm hn))
    (PresentedGroup.ext fun b => by
      cases b
      · exact (congrArg (toBaumslagSolitar m n hm hn) (ofBaumslagSolitar_of_false m n hm hn)).trans
          ((toBaumslagSolitar_of m n hm hn (ofAdd 1)).trans (by simp))
      · exact (congrArg (toBaumslagSolitar m n hm hn) (ofBaumslagSolitar_of_true m n hm hn)).trans
          (toBaumslagSolitar_edge_true m n hm hn))

@[simp] theorem baumslagSolitarEquiv_of (c : Multiplicative ℤ) :
    baumslagSolitarEquiv m n hm hn (of ∅ () c) = PresentedGroup.of false ^ c.toAdd :=
  toBaumslagSolitar_of m n hm hn c

@[simp] theorem baumslagSolitarEquiv_edge_true :
    baumslagSolitarEquiv m n hm hn (edge ∅ ((), true)) = PresentedGroup.of true :=
  toBaumslagSolitar_edge_true m n hm hn

@[simp] theorem baumslagSolitarEquiv_edge_false :
    baumslagSolitarEquiv m n hm hn (edge ∅ ((), false)) = (PresentedGroup.of true)⁻¹ :=
  toBaumslagSolitar_edge_false m n hm hn

@[simp] theorem baumslagSolitarEquiv_symm_of_false :
    (baumslagSolitarEquiv m n hm hn).symm (PresentedGroup.of false) = of ∅ () (ofAdd (1 : ℤ)) :=
  ofBaumslagSolitar_of_false m n hm hn

@[simp] theorem baumslagSolitarEquiv_symm_of_true :
    (baumslagSolitarEquiv m n hm hn).symm (PresentedGroup.of true) = edge ∅ ((), true) :=
  ofBaumslagSolitar_of_true m n hm hn

end π₁Tree

/-! ### The segment: amalgams of infinite cyclic groups -/

/-- The segment of infinite cyclic groups: two vertices joined by an edge, with vertex and edge
groups `ℤ`, whose edge group maps to the vertex group at `false` by `(· ^ m)` and to the vertex
group at `true` by `(· ^ n)`. Its fundamental group is the amalgam `⟨x, y ∣ x ^ m = y ^ n⟩`. -/
@[expose] def cyclicAmalgam : GraphOfGroups.{0, 0, 0, 0} SerreGraph.segment :=
  segment (zpowGroupHom (α := Multiplicative ℤ) m) (zpowGroupHom (α := Multiplicative ℤ) n)
    (zpow_left_injective hm) (zpow_left_injective hn)

@[simp] theorem cyclicAmalgam_ω_false :
    (cyclicAmalgam m n hm hn).ω false = zpowGroupHom (α := Multiplicative ℤ) n := (rfl)

@[simp] theorem cyclicAmalgam_ω_true :
    (cyclicAmalgam m n hm hn).ω true = zpowGroupHom (α := Multiplicative ℤ) m := (rfl)

@[simp] theorem cyclicAmalgam_α_false :
    (cyclicAmalgam m n hm hn).α false = zpowGroupHom (α := Multiplicative ℤ) m :=
  segment_α_false ..

@[simp] theorem cyclicAmalgam_α_true :
    (cyclicAmalgam m n hm hn).α true = zpowGroupHom (α := Multiplicative ℤ) n :=
  segment_α_true ..

/-- The relator `x ^ m y ^ (-n)` of the amalgam `⟨x, y ∣ x ^ m = y ^ n⟩` in the free group on
`x = false` and `y = true`. -/
def cyclicAmalgamRelator : FreeGroup Bool :=
  FreeGroup.of false ^ m * (FreeGroup.of true ^ n)⁻¹

@[simp] theorem lift_cyclicAmalgamRelator {H : Type*} [Group H] (f : Bool → H) :
    FreeGroup.lift f (cyclicAmalgamRelator m n) = f false ^ m * (f true ^ n)⁻¹ := by
  simp [cyclicAmalgamRelator]

/-- The defining relation `x ^ m = y ^ n` of the amalgam `⟨x, y ∣ x ^ m = y ^ n⟩`. -/
theorem cyclicAmalgamRelator_relation :
    (PresentedGroup.of false ^ m : PresentedGroup {cyclicAmalgamRelator m n}) =
      PresentedGroup.of true ^ n := by
  have h := PresentedGroup.one_of_mem (rels := {cyclicAmalgamRelator m n}) rfl
  rw [← PresentedGroup.lift_of_eq_mk, lift_cyclicAmalgamRelator] at h
  exact mul_inv_eq_one.1 h

/-- The defining relation of `⟨x, y ∣ x ^ m = y ^ n⟩` on all powers of the generators: the
image of `c ^ m` under `ℤ → ⟨x⟩` is the image of `c ^ n` under `ℤ → ⟨y⟩`, for every `c` in the
infinite cyclic group. -/
private theorem zpowersHom_of_false_zpow_eq (c : Multiplicative ℤ) :
    (zpowersHom _ (PresentedGroup.of false) (c ^ m) :
      PresentedGroup {cyclicAmalgamRelator m n}) =
      zpowersHom _ (PresentedGroup.of true) (c ^ n) := by
  have h := congrArg (· ^ c.toAdd) (cyclicAmalgamRelator_relation m n)
  simpa only [map_zpow, zpowersHom_apply, ← zpow_mul, mul_comm c.toAdd] using h

/-- The maps from the two vertex groups of the segment of infinite cyclic groups to
`⟨x, y ∣ x ^ m = y ^ n⟩`, sending the generators to `x` and to `y`. -/
private noncomputable def cyclicAmalgamVertexHom : ∀ b : SerreGraph.segment.V,
    (cyclicAmalgam m n hm hn).vertexGroup b →* PresentedGroup {cyclicAmalgamRelator m n}
  | false => zpowersHom _ (PresentedGroup.of false)
  | true => zpowersHom _ (PresentedGroup.of true)

namespace π₁Tree

variable {T : Set SerreGraph.segment.E}

/-- The map from the fundamental group of the segment of infinite cyclic groups to
`⟨x, y ∣ x ^ m = y ^ n⟩`: the generators of the vertex groups map to `x` and to `y`, and the
darts to `1`. -/
private noncomputable def toCyclicAmalgam :
    π₁Tree (cyclicAmalgam m n hm hn) T →* PresentedGroup {cyclicAmalgamRelator m n} :=
  lift (cyclicAmalgamVertexHom m n hm hn) (fun _ => 1) (fun _ _ => rfl) (fun _ => by simp)
    -- The edge group of both darts of the segment is `Multiplicative ℤ` by definition.
    (fun e (c : Multiplicative ℤ) => by
      simp only [one_mul, inv_one, mul_one]
      cases e
      · simp only [cyclicAmalgam_ω_false, cyclicAmalgam_α_false]
        exact (zpowersHom_of_false_zpow_eq m n c).symm
      · simp only [cyclicAmalgam_ω_true, cyclicAmalgam_α_true]
        exact zpowersHom_of_false_zpow_eq m n c)

private theorem toCyclicAmalgam_of_false (c : Multiplicative ℤ) :
    toCyclicAmalgam m n hm hn (of T false c) = PresentedGroup.of false ^ c.toAdd :=
  (lift_of (𝔸 := cyclicAmalgam m n hm hn) (T := T) _ _ _ _ _ false c).trans
    (zpowersHom_apply ..)

private theorem toCyclicAmalgam_of_true (c : Multiplicative ℤ) :
    toCyclicAmalgam m n hm hn (of T true c) = PresentedGroup.of true ^ c.toAdd :=
  (lift_of (𝔸 := cyclicAmalgam m n hm hn) (T := T) _ _ _ _ _ true c).trans
    (zpowersHom_apply ..)

private theorem toCyclicAmalgam_edge (e : SerreGraph.segment.E) :
    toCyclicAmalgam m n hm hn (edge T e) = 1 :=
  lift_edge (𝔸 := cyclicAmalgam m n hm hn) (T := T) _ _ _ _ _ e

variable (T) in
/-- The generators of the two vertex groups of the segment of infinite cyclic groups, in its
fundamental group. -/
private noncomputable def cyclicAmalgamGen : Bool → π₁Tree (cyclicAmalgam m n hm hn) T
  | false => of T false (ofAdd (1 : ℤ))
  | true => of T true (ofAdd (1 : ℤ))

/-- The inverse map from `⟨x, y ∣ x ^ m = y ^ n⟩` to the fundamental group of the segment of
infinite cyclic groups relative to a nonempty set of darts. -/
private noncomputable def ofCyclicAmalgam (hT : T.Nonempty) :
    PresentedGroup {cyclicAmalgamRelator m n} →* π₁Tree (cyclicAmalgam m n hm hn) T :=
  PresentedGroup.toGroup (f := cyclicAmalgamGen m n hm hn T) (by
    rintro _ rfl
    rw [lift_cyclicAmalgamRelator, mul_inv_eq_one]
    -- Both sides are the image of the generator of the edge group: the boundary maps are
    -- `c ↦ c ^ m` and `c ↦ c ^ n` by definition.
    exact ((map_zpow (of (𝔸 := cyclicAmalgam m n hm hn) T false) (ofAdd (1 : ℤ)) m).symm.trans
      (of_true_eq_of_false hT (ofAdd (1 : ℤ))).symm).trans
      (map_zpow (of (𝔸 := cyclicAmalgam m n hm hn) T true) (ofAdd (1 : ℤ)) n))

private theorem ofCyclicAmalgam_of_false (hT : T.Nonempty) :
    ofCyclicAmalgam m n hm hn hT (PresentedGroup.of false) = of T false (ofAdd (1 : ℤ)) :=
  PresentedGroup.toGroup.of _

private theorem ofCyclicAmalgam_of_true (hT : T.Nonempty) :
    ofCyclicAmalgam m n hm hn hT (PresentedGroup.of true) = of T true (ofAdd (1 : ℤ)) :=
  PresentedGroup.toGroup.of _

/-- The fundamental group of the segment of infinite cyclic groups with boundary maps `(· ^ m)`
and `(· ^ n)`, relative to a nonempty set `T` of darts (for instance its maximal tree), is the
amalgam `⟨x, y ∣ x ^ m = y ^ n⟩`: the generators of the vertex groups at `false` and at `true`
correspond to `x` and to `y`, and both darts are trivial. -/
noncomputable def cyclicAmalgamEquiv (hT : T.Nonempty) :
    π₁Tree (cyclicAmalgam m n hm hn) T ≃* PresentedGroup {cyclicAmalgamRelator m n} :=
  MonoidHom.toMulEquiv (toCyclicAmalgam m n hm hn) (ofCyclicAmalgam m n hm hn hT)
    (hom_ext (fun b => by
        -- Each vertex group is `Multiplicative ℤ` by definition, so maps out of it agree when
        -- they agree on the generator.
        cases b
        · exact MonoidHom.ext_mint <| (congrArg (ofCyclicAmalgam m n hm hn hT)
            (toCyclicAmalgam_of_false m n hm hn (ofAdd 1))).trans
            ((congrArg _ (by simp)).trans (ofCyclicAmalgam_of_false m n hm hn hT))
        · exact MonoidHom.ext_mint <| (congrArg (ofCyclicAmalgam m n hm hn hT)
            (toCyclicAmalgam_of_true m n hm hn (ofAdd 1))).trans
            ((congrArg _ (by simp)).trans (ofCyclicAmalgam_of_true m n hm hn hT)))
      fun e => (congrArg (ofCyclicAmalgam m n hm hn hT) (toCyclicAmalgam_edge m n hm hn e)).trans
        ((map_one _).trans (edge_segment_eq_one hT e).symm))
    (PresentedGroup.ext fun b => by
      cases b
      · exact (congrArg (toCyclicAmalgam m n hm hn) (ofCyclicAmalgam_of_false m n hm hn hT)).trans
          ((toCyclicAmalgam_of_false m n hm hn (ofAdd 1)).trans (by simp))
      · exact (congrArg (toCyclicAmalgam m n hm hn) (ofCyclicAmalgam_of_true m n hm hn hT)).trans
          ((toCyclicAmalgam_of_true m n hm hn (ofAdd 1)).trans (by simp)))

@[simp] theorem cyclicAmalgamEquiv_of_false (hT : T.Nonempty) (c : Multiplicative ℤ) :
    cyclicAmalgamEquiv m n hm hn hT (of T false c) = PresentedGroup.of false ^ c.toAdd :=
  toCyclicAmalgam_of_false m n hm hn c

@[simp] theorem cyclicAmalgamEquiv_of_true (hT : T.Nonempty) (c : Multiplicative ℤ) :
    cyclicAmalgamEquiv m n hm hn hT (of T true c) = PresentedGroup.of true ^ c.toAdd :=
  toCyclicAmalgam_of_true m n hm hn c

@[simp] theorem cyclicAmalgamEquiv_edge (hT : T.Nonempty) (e : SerreGraph.segment.E) :
    cyclicAmalgamEquiv m n hm hn hT (edge T e) = 1 :=
  toCyclicAmalgam_edge m n hm hn e

@[simp] theorem cyclicAmalgamEquiv_symm_of_false (hT : T.Nonempty) :
    (cyclicAmalgamEquiv m n hm hn hT).symm (PresentedGroup.of false) =
      of T false (ofAdd (1 : ℤ)) :=
  ofCyclicAmalgam_of_false m n hm hn hT

@[simp] theorem cyclicAmalgamEquiv_symm_of_true (hT : T.Nonempty) :
    (cyclicAmalgamEquiv m n hm hn hT).symm (PresentedGroup.of true) =
      of T true (ofAdd (1 : ℤ)) :=
  ofCyclicAmalgam_of_true m n hm hn hT

end π₁Tree

end GraphOfGroups

end TauCeti
