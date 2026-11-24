/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hive.Octahedron.Recurrence
public import TauCeti.Topology.PL.Map
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Unit-cell excavation schedules, linear branches, and piecewise-affineness

Every section-to-section transition `sectionTransition hn τ₁ τ₂` of Henriques–Kamnitzer's bounded
octahedron recurrence factors into single unit-cell updates ("excavations"):

1. **Legal excavation steps and schedule independence** (`IsExcavationSite`, `excavateSection`,
   `excavateData`, `ExcavationSchedule`, `ExcavationSchedule.eval_eq_sectionTransition`): a grid
   point `(x₀, y₀)` is a legal upward excavation site on `τ` when every grid neighbour has height
   `τ x₀ y₀ + 1`; advancing `τ x₀ y₀` to `τ x₀ y₀ + 2` updates `F x₀ y₀` by a single octahedron
   step, and **every** legal schedule from `τ₁` to `τ₂` evaluates to `sectionTransition hn τ₁ τ₂`
   and has length `excavationVolume τ₁ τ₂`.
2. **Termination of upward excavation** (`exists_excavationSite_of_lt`, `ExcavationSchedule.ofLe`):
   whenever `τ₁ < τ₂`, there exists a legal excavation site whose update remains `≤ τ₂` and
   strictly decreases `excavationVolume` by `1`, yielding a legal schedule from `τ₁` to `τ₂`.
3. **Linear branches and tie agreement** (`stepBranchLinear`, `stepBranchLinear_eq_of_tie`,
   `scheduleBranchLinear`, `exists_branchWord_scheduleBranchLinear`, `map_scheduleBranchLinear`):
   for any `A`-module `R`, each choice of `max` branch in a single step is an `A`-linear map (in
   particular `ℤ`-linear over any `AddCommGroup`, so composed branches have integer matrix entries),
   compatible with any `AddMonoidHom`, and the two branches agree along the tie hyperplane
   `branchSum hn true F x₀ y₀ = branchSum hn false F x₀ y₀`.
4. **Global piecewise-affineness and continuity** (`isPiecewiseAffineOn_excavateData`,
   `isPiecewiseAffineOn_sectionTransition`, `isPiecewiseAffineOn_associatorTransition`,
   `continuous_sectionTransition`, `continuous_associatorTransition`): over `ℝ`, every section
   transition (whether upward, downward, or mixed, via `τ₁ → τ₁ ⊔ τ₂ → τ₂`) and every
   `associatorTransition n` satisfies `TauCeti.IsPiecewiseAffineOn` on `Set.univ`, hence is
   globally continuous.

## References

* A. Henriques and J. Kamnitzer, *The octahedron recurrence and $\mathfrak{gl}_n$ crystals*,
  Adv. Math. **206** (2006), 211–249, §3.
* A. Knutson, T. Tao, and C. Woodward, *A positive proof of the Littlewood–Richardson rule using
  the octahedron recurrence*, Electron. J. Combin. **11** (2004), R61, §5.
-/

public section

open scoped BigOperators

namespace TauCeti.Hive.Octahedron

section Excavation

variable {n : ℕ}

/-- A grid point `(x₀, y₀)` is a legal upward unit-cell excavation site on `τ : Section n` when
every grid-adjacent point `(x', y')` has height `τ x₀ y₀ + 1`. -/
def IsExcavationSite (τ : Section n) (x₀ y₀ : Fin (n + 1)) : Prop :=
  ∀ x' y' : Fin (n + 1), GridAdj x₀ y₀ x' y' → τ x' y' = τ x₀ y₀ + 1

theorem isExcavationSite_def (τ : Section n) (x₀ y₀ : Fin (n + 1)) :
    IsExcavationSite τ x₀ y₀ ↔
      ∀ x' y' : Fin (n + 1), GridAdj x₀ y₀ x' y' → τ x' y' = τ x₀ y₀ + 1 := by
  unfold IsExcavationSite; rfl

instance (τ : Section n) (x₀ y₀ : Fin (n + 1)) : Decidable (IsExcavationSite τ x₀ y₀) :=
  decidable_of_iff _ (isExcavationSite_def τ x₀ y₀).symm

/-- Advance `τ` at a legal excavation site `(x₀, y₀)` by `+2`, excavating one unit cell. -/
def excavateSection (τ : Section n) (x₀ y₀ : Fin (n + 1))
    (hsite : IsExcavationSite τ x₀ y₀) : Section n :=
  Section.ofDistLeOne (fun x y => if x = x₀ ∧ y = y₀ then τ x₀ y₀ + 2 else τ x y)
    (fun x y => by
      split_ifs with h
      · rcases h with ⟨hx, hy⟩; subst hx; subst hy
        obtain ⟨k, hk⟩ := τ.even_sum x y
        exact ⟨k + 1, by linarith⟩
      · exact τ.even_sum x y)
    (fun {x₁ y₁ x₂ y₂} hadj => by
      have hne : ¬ (x₁ = x₂ ∧ y₁ = y₂) := by
        rintro ⟨hx, hy⟩; subst hx; subst hy
        rw [gridAdj_def] at hadj; simp at hadj
      by_cases h₁ : x₁ = x₀ ∧ y₁ = y₀ <;> by_cases h₂ : x₂ = x₀ ∧ y₂ = y₀ <;>
        simp only [h₁, h₂, ↓reduceIte]
      · exfalso; exact hne ⟨h₁.1.trans h₂.1.symm, h₁.2.trans h₂.2.symm⟩
      · rcases h₁ with ⟨hx, hy⟩; subst hx; subst hy
        rw [(isExcavationSite_def τ x₁ y₁).mp hsite x₂ y₂ hadj]
        simp only [Int.abs_eq_natAbs]; omega
      · rcases h₂ with ⟨hx, hy⟩; subst hx; subst hy
        rw [(isExcavationSite_def τ x₂ y₂).mp hsite x₁ y₁ hadj.symm]
        simp only [Int.abs_eq_natAbs]; omega
      · exact (τ.abs_sub_eq_one hadj).le)

@[simp] theorem excavateSection_apply (τ : Section n) (x₀ y₀ : Fin (n + 1))
    (hsite : IsExcavationSite τ x₀ y₀) (x y : Fin (n + 1)) :
    excavateSection τ x₀ y₀ hsite x y = if x = x₀ ∧ y = y₀ then τ x₀ y₀ + 2 else τ x y := by
  unfold excavateSection; exact Section.ofDistLeOne_apply _ _ _ x y

theorem le_excavateSection (τ : Section n) (x₀ y₀ : Fin (n + 1))
    (hsite : IsExcavationSite τ x₀ y₀) : τ ≤ excavateSection τ x₀ y₀ hsite := by
  rw [Section.le_def]; intro x y
  rw [excavateSection_apply]
  split_ifs with h
  · rcases h with ⟨hx, hy⟩; subst hx; subst hy; omega
  · exact le_rfl

/-- Single-cell data update at `(x₀, y₀)` under the bounded octahedron recurrence. -/
def excavateData {R : Type*} [AddCommGroup R] [SemilatticeSup R] (hn : 1 ≤ n)
    (x₀ y₀ : Fin (n + 1)) (F : Fin (n + 1) → Fin (n + 1) → R) (x y : Fin (n + 1)) : R :=
  if x = x₀ ∧ y = y₀ then spatialSup hn F x₀ y₀ - F x₀ y₀ else F x y

@[simp] theorem excavateData_apply {R : Type*} [AddCommGroup R] [SemilatticeSup R] (hn : 1 ≤ n)
    (x₀ y₀ : Fin (n + 1)) (F : Fin (n + 1) → Fin (n + 1) → R) (x y : Fin (n + 1)) :
    excavateData hn x₀ y₀ F x y =
      if x = x₀ ∧ y = y₀ then spatialSup hn F x₀ y₀ - F x₀ y₀ else F x y := by
  unfold excavateData; rfl

/-- One legal unit-cell excavation step agrees identically with `sectionTransition`. -/
theorem sectionTransition_excavateSection {R : Type*} [AddCommGroup R] [SemilatticeSup R]
    (hn : 1 ≤ n) (τ : Section n) (x₀ y₀ : Fin (n + 1)) (hsite : IsExcavationSite τ x₀ y₀)
    (F : Fin (n + 1) → Fin (n + 1) → R) :
    sectionTransition hn τ (excavateSection τ x₀ y₀ hsite) F = excavateData hn x₀ y₀ F := by
  funext x y
  by_cases hxy : x = x₀ ∧ y = y₀
  · rcases hxy with ⟨hx, hy⟩; subst hx; subst hy
    rw [sectionTransition_apply, excavateData_apply, ite_eq_left ⟨rfl, rfl⟩]
    obtain ⟨k, hk⟩ := τ.even_sum x y
    have hodd : Odd ((x.val : ℤ) + y.val + (τ x y + 1)) := ⟨k, by linarith⟩
    have hrec := (satisfiesRecurrence_def hn _).mp
      (satisfiesRecurrence_evolveFromSection hn τ F) x y (τ x y + 1) hodd
    have hpt_top : (excavateSection τ x y hsite).point x y =
        ⟨x, y, τ x y + 1 + 1, even_add_one_of_odd hodd⟩ := by
      ext
      · simp
      · simp
      · simp only [Section.point_t, excavateSection_apply, and_self, ↓reduceIte]; ring
    have hpt_bot : (⟨x, y, τ x y + 1 - 1, even_sub_one_of_odd hodd⟩ : SpaceTimePoint n) =
        τ.point x y := by
      ext <;> simp
    have hadj_pt {x' y' : Fin (n + 1)} (hadj : GridAdj x y x' y') :
        (⟨x', y', τ x y + 1, even_of_gridAdj_of_odd hadj hodd⟩ : SpaceTimePoint n) =
          τ.point x' y' := by
      ext
      · simp
      · simp
      · simp [(isExcavationSite_def τ x y).mp hsite x' y' hadj]
    have hsup : paritySpatialSup hn (evolveFromSection hn τ F) x y (τ x y + 1) hodd =
        spatialSup hn F x y :=
      paritySpatialSup_eq_spatialSup_of_eq hn hodd fun hadj => by
        rw [hadj_pt hadj, evolveFromSection_point]
    rw [hpt_top, hrec, hpt_bot, hsup, evolveFromSection_point]
  · rw [sectionTransition_eq_self_of_eq hn F (by simp [hxy]), excavateData_apply,
      ite_eq_right hxy]

/-- Directed upward unit-cell count above `τ₁` and below `τ₂` (matching the total number of unit
cells between `τ₁` and `τ₂` when `τ₁ ≤ τ₂`, and evaluating to `0` wherever `τ₂ ≤ τ₁`). -/
def excavationVolume (τ₁ τ₂ : Section n) : ℕ :=
  ∑ q : Fin (n + 1) × Fin (n + 1), ((τ₂ q.1 q.2 - τ₁ q.1 q.2) / 2).toNat

theorem excavationVolume_def (τ₁ τ₂ : Section n) :
    excavationVolume τ₁ τ₂ =
      ∑ q : Fin (n + 1) × Fin (n + 1), ((τ₂ q.1 q.2 - τ₁ q.1 q.2) / 2).toNat := by
  unfold excavationVolume; rfl

@[simp] theorem excavationVolume_self (τ : Section n) : excavationVolume τ τ = 0 := by
  unfold excavationVolume; simp

theorem excavationVolume_excavateSection {τ₁ τ₂ : Section n} {x₀ y₀ : Fin (n + 1)}
    {hsite : IsExcavationSite τ₁ x₀ y₀} (hle : excavateSection τ₁ x₀ y₀ hsite ≤ τ₂) :
    excavationVolume (excavateSection τ₁ x₀ y₀ hsite) τ₂ + 1 = excavationVolume τ₁ τ₂ := by
  have hgap : τ₁ x₀ y₀ + 2 ≤ τ₂ x₀ y₀ := by
    have h := Section.le_def.mp hle x₀ y₀
    simpa [excavateSection_apply] using h
  unfold excavationVolume
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (x₀, y₀)),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ (x₀, y₀))]
  have hrest :
      (∑ q ∈ Finset.univ.erase (x₀, y₀),
        ((τ₂ q.1 q.2 - excavateSection τ₁ x₀ y₀ hsite q.1 q.2) / 2).toNat) =
      ∑ q ∈ Finset.univ.erase (x₀, y₀), ((τ₂ q.1 q.2 - τ₁ q.1 q.2) / 2).toNat := by
    refine Finset.sum_congr rfl fun q hq => ?_
    have hneq : ¬ (q.1 = x₀ ∧ q.2 = y₀) := by
      have := Finset.ne_of_mem_erase hq
      rintro ⟨hx, hy⟩; exact this (Prod.ext hx hy)
    simp [excavateSection_apply, hneq]
  dsimp only
  rw [hrest, excavateSection_apply, ite_eq_left ⟨rfl, rfl⟩]
  omega

/-- A finite sequence of legal unit-cell excavations transforming `τ₁` into `τ₂`. -/
inductive ExcavationSchedule : Section n → Section n → Type
  | nil (τ : Section n) : ExcavationSchedule τ τ
  | cons {τ₁ τ₂ : Section n} (x₀ y₀ : Fin (n + 1)) (hsite : IsExcavationSite τ₁ x₀ y₀)
      (rest : ExcavationSchedule (excavateSection τ₁ x₀ y₀ hsite) τ₂) :
      ExcavationSchedule τ₁ τ₂

namespace ExcavationSchedule

/-- Number of unit-cell excavation steps in a schedule. -/
def length {τ₁ τ₂ : Section n} : ExcavationSchedule τ₁ τ₂ → ℕ
  | nil _ => 0
  | cons _ _ _ rest => rest.length + 1

@[simp] theorem length_nil (τ : Section n) : (nil τ).length = 0 := by
  rw [length]

@[simp] theorem length_cons {τ₁ τ₂ : Section n} (x₀ y₀ : Fin (n + 1))
    (hsite : IsExcavationSite τ₁ x₀ y₀)
    (rest : ExcavationSchedule (excavateSection τ₁ x₀ y₀ hsite) τ₂) :
    (cons x₀ y₀ hsite rest).length = rest.length + 1 := by
  rw [length]

/-- Every legal excavation schedule moves monotonically upward (`τ₁ ≤ τ₂`). -/
theorem le {τ₁ τ₂ : Section n} : ExcavationSchedule τ₁ τ₂ → τ₁ ≤ τ₂
  | nil _ => le_rfl
  | cons x₀ y₀ hsite rest => (le_excavateSection _ x₀ y₀ hsite).trans rest.le

/-- Every legal excavation schedule from `τ₁` to `τ₂` has length equal to `excavationVolume τ₁ τ₂`,
independent of the order of steps. -/
theorem length_eq_excavationVolume {τ₁ τ₂ : Section n} (S : ExcavationSchedule τ₁ τ₂) :
    S.length = excavationVolume τ₁ τ₂ := by
  induction S with
  | nil _ => simp
  | cons x₀ y₀ hsite rest ih =>
    rw [length_cons, ih, excavationVolume_excavateSection rest.le]

/-- Evaluate the recurrence along a legal excavation schedule. -/
def eval {R : Type*} [AddCommGroup R] [SemilatticeSup R] (hn : 1 ≤ n) {τ₁ τ₂ : Section n} :
    ExcavationSchedule τ₁ τ₂ →
      (Fin (n + 1) → Fin (n + 1) → R) → (Fin (n + 1) → Fin (n + 1) → R)
  | nil _, F => F
  | cons x₀ y₀ _ rest, F => rest.eval hn (excavateData hn x₀ y₀ F)

@[simp] theorem eval_nil {R : Type*} [AddCommGroup R] [SemilatticeSup R] (hn : 1 ≤ n)
    (τ : Section n) : (nil τ).eval (R := R) hn = id := by
  ext F x y; rw [eval]; rfl

@[simp] theorem eval_cons {R : Type*} [AddCommGroup R] [SemilatticeSup R] (hn : 1 ≤ n)
    {τ₁ τ₂ : Section n} (x₀ y₀ : Fin (n + 1)) (hsite : IsExcavationSite τ₁ x₀ y₀)
    (rest : ExcavationSchedule (excavateSection τ₁ x₀ y₀ hsite) τ₂)
    (F : Fin (n + 1) → Fin (n + 1) → R) :
    (cons x₀ y₀ hsite rest).eval hn F = rest.eval hn (excavateData hn x₀ y₀ F) := by
  rw [eval]

/-- Schedule independence: **every** legal unit-cell excavation schedule from `τ₁` to `τ₂`
computes `sectionTransition hn τ₁ τ₂`. -/
theorem eval_eq_sectionTransition {R : Type*} [AddCommGroup R] [SemilatticeSup R] (hn : 1 ≤ n)
    {τ₁ τ₂ : Section n} (S : ExcavationSchedule τ₁ τ₂) (F : Fin (n + 1) → Fin (n + 1) → R) :
    S.eval hn F = sectionTransition hn τ₁ τ₂ F := by
  induction S generalizing F with
  | nil _ =>
    simp [eval_nil, sectionTransition_refl]
  | cons x₀ y₀ hsite rest ih =>
    rw [eval_cons, ih, ← sectionTransition_excavateSection hn _ x₀ y₀ hsite F,
      ← Equiv.trans_apply, sectionTransition_trans]

end ExcavationSchedule

/-- Whenever `τ₁ < τ₂`, there exists a legal upward excavation site `(x₀, y₀)` on `τ₁` whose step
remains `≤ τ₂` and decreases `excavationVolume` by `1`. -/
theorem exists_excavationSite_of_lt {τ₁ τ₂ : Section n} (hlt : τ₁ < τ₂) :
    ∃ x₀ y₀ : Fin (n + 1), ∃ hsite : IsExcavationSite τ₁ x₀ y₀,
      excavateSection τ₁ x₀ y₀ hsite ≤ τ₂ ∧
        excavationVolume (excavateSection τ₁ x₀ y₀ hsite) τ₂ + 1 = excavationVolume τ₁ τ₂ := by
  obtain ⟨hle, hne⟩ := lt_iff_le_and_ne.mp hlt
  rw [Section.le_def] at hle
  let D : Finset (Fin (n + 1) × Fin (n + 1)) :=
    Finset.univ.filter fun q => τ₁ q.1 q.2 < τ₂ q.1 q.2
  have hD : D.Nonempty := by
    by_contra hnot
    rw [Finset.not_nonempty_iff_eq_empty] at hnot
    apply hne; ext x y
    have hmem : (x, y) ∉ D := by rw [hnot]; simp
    have : ¬ τ₁ x y < τ₂ x y := by simpa [D] using hmem
    exact le_antisymm (hle x y) (not_lt.mp this)
  obtain ⟨⟨x₀, y₀⟩, hmem₀, hmin₀⟩ := Finset.exists_min_image D (fun q => τ₁ q.1 q.2) hD
  have hlt₀ : τ₁ x₀ y₀ < τ₂ x₀ y₀ := (Finset.mem_filter.mp hmem₀).2
  obtain ⟨k₁, hk₁⟩ := τ₁.even_sum x₀ y₀
  obtain ⟨k₂, hk₂⟩ := τ₂.even_sum x₀ y₀
  have hgap : τ₁ x₀ y₀ + 2 ≤ τ₂ x₀ y₀ := by omega
  have hsite : IsExcavationSite τ₁ x₀ y₀ := by
    rw [isExcavationSite_def]
    intro x' y' hadj
    have hs1 := τ₁.slope_eq_one hadj
    have hs2 := τ₂.slope_eq_one hadj
    rcases (by omega : τ₁ x' y' = τ₁ x₀ y₀ + 1 ∨ τ₁ x' y' = τ₁ x₀ y₀ - 1) with hup | hdn
    · exact hup
    · exfalso
      have hlt' : τ₁ x' y' < τ₂ x' y' := by omega
      have hmin' := hmin₀ (x', y') (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt'⟩)
      dsimp at hmin'; omega
  have hstep_le : excavateSection τ₁ x₀ y₀ hsite ≤ τ₂ := by
    rw [Section.le_def]; intro x y
    rw [excavateSection_apply]
    split_ifs with h
    · rcases h with ⟨hx, hy⟩; subst hx; subst hy; exact hgap
    · exact hle x y
  exact ⟨x₀, y₀, hsite, hstep_le, excavationVolume_excavateSection hstep_le⟩

/-- Construct a (`noncomputable`) legal upward unit-cell excavation schedule from `τ₁` to `τ₂`
(`τ₁ ≤ τ₂`) via choice, terminating in `excavationVolume τ₁ τ₂` steps. -/
noncomputable def ExcavationSchedule.ofLe {τ₁ τ₂ : Section n} (hle : τ₁ ≤ τ₂) :
    ExcavationSchedule τ₁ τ₂ :=
  if hne : τ₁ = τ₂ then
    hne ▸ ExcavationSchedule.nil τ₁
  else
    have hlt := lt_of_le_of_ne hle hne
    let x₀ := Classical.choose (exists_excavationSite_of_lt hlt)
    let h1 := Classical.choose_spec (exists_excavationSite_of_lt hlt)
    let y₀ := Classical.choose h1
    let h2 := Classical.choose_spec h1
    let hsite := Classical.choose h2
    let hspec := Classical.choose_spec h2
    have _hdec : excavationVolume (excavateSection τ₁ x₀ y₀ hsite) τ₂ <
        excavationVolume τ₁ τ₂ := Nat.lt_of_succ_le (Nat.le_of_eq hspec.2)
    ExcavationSchedule.cons x₀ y₀ hsite (ExcavationSchedule.ofLe hspec.1)
termination_by excavationVolume τ₁ τ₂

/-- `A`-linear branch map of a single excavation step `(x₀, y₀)` along branch `b : Bool` for any
`A`-module `R` (in particular `A = ℤ` on any `AddCommGroup R`, where its matrix entries are
integers). -/
def stepBranchLinear (A : Type*) [Semiring A] {R : Type*} [AddCommGroup R] [Module A R]
    (hn : 1 ≤ n) (x₀ y₀ : Fin (n + 1)) (b : Bool) :
    (Fin (n + 1) → Fin (n + 1) → R) →ₗ[A] (Fin (n + 1) → Fin (n + 1) → R) where
  toFun F x y := if x = x₀ ∧ y = y₀ then branchSum hn b F x₀ y₀ - F x₀ y₀ else F x y
  map_add' F G := by
    funext x y; simp only [Pi.add_apply]; split_ifs
    · simp only [branchSum_apply, Pi.add_apply]; abel
    · rfl
  map_smul' c F := by
    funext x y; simp only [Pi.smul_apply, RingHom.id_apply]; split_ifs
    · simp only [branchSum_apply, Pi.smul_apply, smul_sub, smul_add]
    · rfl

@[simp] theorem stepBranchLinear_apply (A : Type*) [Semiring A] {R : Type*} [AddCommGroup R]
    [Module A R] (hn : 1 ≤ n) (x₀ y₀ : Fin (n + 1)) (b : Bool)
    (F : Fin (n + 1) → Fin (n + 1) → R) (x y : Fin (n + 1)) :
    stepBranchLinear A hn x₀ y₀ b F x y =
      if x = x₀ ∧ y = y₀ then branchSum hn b F x₀ y₀ - F x₀ y₀ else F x y := by
  unfold stepBranchLinear; rfl

/-- Along the tie hyperplane `branchSum hn true F x₀ y₀ = branchSum hn false F x₀ y₀`, both linear
branches of a single step agree identically. -/
theorem stepBranchLinear_eq_of_tie (A : Type*) [Semiring A] {R : Type*} [AddCommGroup R]
    [Module A R] (hn : 1 ≤ n) (x₀ y₀ : Fin (n + 1)) {F : Fin (n + 1) → Fin (n + 1) → R}
    (htie : branchSum hn true F x₀ y₀ = branchSum hn false F x₀ y₀) :
    stepBranchLinear A hn x₀ y₀ true F = stepBranchLinear A hn x₀ y₀ false F := by
  ext x y; simp [htie]

/-- Composed `A`-linear branch map along an excavation schedule `S` for a branch word
`w : Fin S.length → Bool`. Over `A = R = ℤ`, this exhibits every linear branch as a `ℤ`-linear map.
-/
def scheduleBranchLinear (A : Type*) [Semiring A] {R : Type*} [AddCommGroup R] [Module A R]
    (hn : 1 ≤ n) {τ₁ τ₂ : Section n} :
    (S : ExcavationSchedule τ₁ τ₂) → (Fin S.length → Bool) →
      ((Fin (n + 1) → Fin (n + 1) → R) →ₗ[A] (Fin (n + 1) → Fin (n + 1) → R))
  | .nil _, _ => LinearMap.id
  | .cons x₀ y₀ hsite rest, w =>
      (scheduleBranchLinear A hn rest
        (fun i => w (Fin.cast (ExcavationSchedule.length_cons x₀ y₀ hsite rest).symm i.succ))).comp
        (stepBranchLinear A hn x₀ y₀ (w ⟨0, by simp⟩))

@[simp] theorem scheduleBranchLinear_nil (A : Type*) [Semiring A] {R : Type*} [AddCommGroup R]
    [Module A R] (hn : 1 ≤ n) (τ : Section n)
    (w : Fin (ExcavationSchedule.nil τ).length → Bool) :
    scheduleBranchLinear (R := R) A hn (.nil τ) w = LinearMap.id := by
  rw [scheduleBranchLinear]

@[simp] theorem scheduleBranchLinear_cons (A : Type*) [Semiring A] {R : Type*} [AddCommGroup R]
    [Module A R] (hn : 1 ≤ n) {τ₁ τ₂ : Section n} (x₀ y₀ : Fin (n + 1))
    (hsite : IsExcavationSite τ₁ x₀ y₀)
    (rest : ExcavationSchedule (excavateSection τ₁ x₀ y₀ hsite) τ₂)
    (w : Fin (ExcavationSchedule.cons x₀ y₀ hsite rest).length → Bool) :
    scheduleBranchLinear (R := R) A hn (.cons x₀ y₀ hsite rest) w =
      (scheduleBranchLinear A hn rest
        (fun i => w (Fin.cast (ExcavationSchedule.length_cons x₀ y₀ hsite rest).symm i.succ))).comp
        (stepBranchLinear A hn x₀ y₀ (w ⟨0, by simp⟩)) := by
  rw [scheduleBranchLinear]

/-- Compatibility of `scheduleBranchLinear` with any additive group homomorphism `φ : R →+ R'` (in
particular `Int.castAddHom ℝ`, showing that the real linear branches are scalar extensions of
integer matrices). -/
theorem map_scheduleBranchLinear (A A' : Type*) {R R' : Type*} [Semiring A] [Semiring A']
    [AddCommGroup R] [AddCommGroup R'] [Module A R] [Module A' R'] (φ : R →+ R')
    (hn : 1 ≤ n) {τ₁ τ₂ : Section n} (S : ExcavationSchedule τ₁ τ₂) (w : Fin S.length → Bool)
    (F : Fin (n + 1) → Fin (n + 1) → R) (x y : Fin (n + 1)) :
    φ (scheduleBranchLinear A hn S w F x y) =
      scheduleBranchLinear A' hn S w (fun x' y' => φ (F x' y')) x y := by
  induction S generalizing F with
  | nil _ => simp
  | cons x₀ y₀ hsite rest ih =>
    rw [scheduleBranchLinear_cons, scheduleBranchLinear_cons, LinearMap.comp_apply,
      LinearMap.comp_apply]
    let b₀ : Bool := w ⟨0, by simp⟩
    have hstep : (fun x' y' => φ (stepBranchLinear A hn x₀ y₀ b₀ F x' y')) =
        stepBranchLinear A' hn x₀ y₀ b₀ (fun x' y' => φ (F x' y')) := by
      funext x' y'
      rw [stepBranchLinear_apply, stepBranchLinear_apply]
      split_ifs
      · simp only [branchSum_apply, map_sub, map_add]
      · rfl
    rw [ih (fun i => w (Fin.cast (ExcavationSchedule.length_cons x₀ y₀ hsite rest).symm i.succ))
      (stepBranchLinear A hn x₀ y₀ b₀ F), hstep]

/-- For every input `F`, some branch word `w : Fin S.length → Bool` realizes `S.eval hn F` as the
exact linear branch map `scheduleBranchLinear A hn S w F`. -/
theorem exists_branchWord_scheduleBranchLinear (A : Type*) [Semiring A] {R : Type*}
    [AddCommGroup R] [Module A R] [LinearOrder R] (hn : 1 ≤ n)
    {τ₁ τ₂ : Section n} (S : ExcavationSchedule τ₁ τ₂) (F : Fin (n + 1) → Fin (n + 1) → R) :
    ∃ w : Fin S.length → Bool, scheduleBranchLinear A hn S w F = S.eval hn F := by
  induction S generalizing F with
  | nil τ =>
    exact ⟨fun i => Fin.elim0 (Fin.cast (ExcavationSchedule.length_nil τ) i), by simp⟩
  | cons x₀ y₀ hsite rest ih =>
    have hstep : ∃ b₀ : Bool, stepBranchLinear A hn x₀ y₀ b₀ F = excavateData hn x₀ y₀ F := by
      rcases le_total (branchSum hn true F x₀ y₀) (branchSum hn false F x₀ y₀) with h | h
      · refine ⟨false, ?_⟩
        ext x y; simp [excavateData_apply, spatialSup_def, sup_eq_right.mpr h]
      · refine ⟨true, ?_⟩
        ext x y; simp [excavateData_apply, spatialSup_def, sup_eq_left.mpr h]
    obtain ⟨b₀, hb₀⟩ := hstep
    obtain ⟨w', hw'⟩ := ih (excavateData hn x₀ y₀ F)
    let hlen := ExcavationSchedule.length_cons x₀ y₀ hsite rest
    let wCons : Fin (rest.length + 1) → Bool := Fin.cons b₀ w'
    refine ⟨fun j => wCons (Fin.cast hlen j), ?_⟩
    rw [scheduleBranchLinear_cons, ExcavationSchedule.eval_cons, LinearMap.comp_apply]
    have h0 : wCons (Fin.cast hlen (⟨0, by simp⟩ :
        Fin (ExcavationSchedule.cons x₀ y₀ hsite rest).length)) = b₀ := by
      simp [wCons]
    have htail : (fun i : Fin rest.length =>
        wCons (Fin.cast hlen (Fin.cast hlen.symm i.succ))) = w' := by
      funext i; simp [wCons]
    rw [h0, htail, hb₀, hw']

private def gridEvalContLinear (x y : Fin (n + 1)) :
    (Fin (n + 1) → Fin (n + 1) → ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) => ℝ) y).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) => Fin (n + 1) → ℝ) x)

private def branchSumContLinear (hn : 1 ≤ n) (b : Bool) (x₀ y₀ : Fin (n + 1)) :
    (Fin (n + 1) → Fin (n + 1) → ℝ) →L[ℝ] ℝ :=
  let p := branchNeighbors hn b x₀ y₀
  gridEvalContLinear p.1.1 p.1.2 + gridEvalContLinear p.2.1 p.2.2

private theorem branchSumContLinear_apply (hn : 1 ≤ n) (b : Bool) (x₀ y₀ : Fin (n + 1))
    (F : Fin (n + 1) → Fin (n + 1) → ℝ) :
    branchSumContLinear hn b x₀ y₀ F = branchSum hn b F x₀ y₀ := by
  simp [branchSumContLinear, gridEvalContLinear, branchSum_apply]

/-- Every single unit-cell excavation step over `ℝ` satisfies `TauCeti.IsPiecewiseAffineOn` on
`Set.univ`. -/
theorem isPiecewiseAffineOn_excavateData (hn : 1 ≤ n) (x₀ y₀ : Fin (n + 1)) :
    TauCeti.IsPiecewiseAffineOn
      (excavateData (R := ℝ) hn x₀ y₀)
      (Set.univ : Set (Fin (n + 1) → Fin (n + 1) → ℝ)) := by
  let L_t := branchSumContLinear hn true x₀ y₀
  let L_f := branchSumContLinear hn false x₀ y₀
  let C : Bool → Set (Fin (n + 1) → Fin (n + 1) → ℝ)
    | true => {F | (L_f - L_t).toContinuousAffineMap F ≤ 0}
    | false => {F | (L_t - L_f).toContinuousAffineMap F ≤ 0}
  let A : Bool → ((Fin (n + 1) → Fin (n + 1) → ℝ) →ᴬ[ℝ] (Fin (n + 1) → Fin (n + 1) → ℝ)) :=
    fun b =>
      (LinearMap.toContinuousLinearMap (stepBranchLinear ℝ hn x₀ y₀ b)).toContinuousAffineMap
  refine TauCeti.isPiecewiseAffineOn_of_finite (ι := Bool) (C := C) (A := A) ?_ ?_ ?_
  · intro b; cases b <;> exact TauCeti.isConvexPolyhedron_setOf_le _
  · intro F _
    rcases le_total (L_t F) (L_f F) with h | h
    · exact Set.mem_iUnion.mpr ⟨false, by simpa [C] using sub_nonpos.mpr h⟩
    · exact Set.mem_iUnion.mpr ⟨true, by simpa [C] using sub_nonpos.mpr h⟩
  · intro b F ⟨_, hFC⟩
    funext x y
    cases b
    · have hle : branchSum hn true F x₀ y₀ ≤ branchSum hn false F x₀ y₀ := by
        simpa [C, L_t, L_f, branchSumContLinear_apply] using hFC
      simp [A, excavateData_apply, spatialSup_def, max_eq_right hle]
    · have hle : branchSum hn false F x₀ y₀ ≤ branchSum hn true F x₀ y₀ := by
        simpa [C, L_t, L_f, branchSumContLinear_apply] using hFC
      simp [A, excavateData_apply, spatialSup_def, max_eq_left hle]

/-- Every legal excavation schedule defines a globally piecewise-affine map on `Set.univ`. -/
theorem ExcavationSchedule.isPiecewiseAffineOn_eval (hn : 1 ≤ n) {τ₁ τ₂ : Section n}
    (S : ExcavationSchedule τ₁ τ₂) :
    TauCeti.IsPiecewiseAffineOn
      (S.eval (R := ℝ) hn)
      (Set.univ : Set (Fin (n + 1) → Fin (n + 1) → ℝ)) := by
  induction S with
  | nil _ =>
    rw [eval_nil]
    exact TauCeti.isPiecewiseAffineOn_continuousAffineMap (ContinuousAffineMap.id ℝ _) Set.univ
  | cons x₀ y₀ hsite rest ih =>
    have heq : (cons x₀ y₀ hsite rest).eval (R := ℝ) hn =
        rest.eval hn ∘ excavateData hn x₀ y₀ := funext fun F => eval_cons hn x₀ y₀ hsite rest F
    rw [heq]
    exact ih.comp (isPiecewiseAffineOn_excavateData hn x₀ y₀) (Set.mapsTo_univ _ _)

private theorem isPiecewiseAffineOn_sectionTransition_of_le (hn : 1 ≤ n)
    {τ₁ τ₂ : Section n} (hle : τ₁ ≤ τ₂) :
    TauCeti.IsPiecewiseAffineOn
      (sectionTransition (R := ℝ) hn τ₁ τ₂)
      (Set.univ : Set (Fin (n + 1) → Fin (n + 1) → ℝ)) := by
  have heq : (⇑(sectionTransition (R := ℝ) hn τ₁ τ₂) :
      (Fin (n + 1) → Fin (n + 1) → ℝ) → _) = (ExcavationSchedule.ofLe hle).eval hn :=
    funext fun F => ((ExcavationSchedule.ofLe hle).eval_eq_sectionTransition hn F).symm
  rw [heq]
  exact (ExcavationSchedule.ofLe hle).isPiecewiseAffineOn_eval hn

/-- For **every** pair of sections `τ₁, τ₂ : Section n` (`1 ≤ n`), the state-transition bijection
`sectionTransition hn τ₁ τ₂` over `ℝ` is globally piecewise affine (`TauCeti.IsPiecewiseAffineOn`)
on `Set.univ`. -/
theorem isPiecewiseAffineOn_sectionTransition (hn : 1 ≤ n) (τ₁ τ₂ : Section n) :
    TauCeti.IsPiecewiseAffineOn
      (sectionTransition (R := ℝ) hn τ₁ τ₂)
      (Set.univ : Set (Fin (n + 1) → Fin (n + 1) → ℝ)) := by
  have hpa₁ := isPiecewiseAffineOn_sectionTransition_of_le hn (le_sup_left : τ₁ ≤ τ₁ ⊔ τ₂)
  have hpa₂ : TauCeti.IsPiecewiseAffineOn
      (sectionTransition (R := ℝ) hn (τ₁ ⊔ τ₂) τ₂) Set.univ := by
    rw [← sectionTransition_timeRev hn (τ₁ ⊔ τ₂) τ₂]
    exact isPiecewiseAffineOn_sectionTransition_of_le hn
      (Section.timeRev_le_timeRev.mpr le_sup_right)
  have hcomp := hpa₂.comp hpa₁ (Set.mapsTo_univ _ _)
  rwa [← Equiv.coe_trans, sectionTransition_trans] at hcomp

/-- `associatorTransition n` over `ℝ` is globally piecewise affine on `Set.univ` for all `n : ℕ`. -/
theorem isPiecewiseAffineOn_associatorTransition (n : ℕ) :
    TauCeti.IsPiecewiseAffineOn
      (associatorTransition (R := ℝ) n)
      (Set.univ : Set (Fin (n + 1) → Fin (n + 1) → ℝ)) := by
  by_cases hn : 1 ≤ n
  · rw [associatorTransition_of_one_le hn]
    exact isPiecewiseAffineOn_sectionTransition hn (lowerSection n) (upperSection n)
  · have hn0 : n = 0 := by omega
    subst hn0
    rw [associatorTransition_zero]
    exact TauCeti.isPiecewiseAffineOn_continuousAffineMap (ContinuousAffineMap.id ℝ _) Set.univ

/-- Every section-to-section state transition over `ℝ` is globally continuous. -/
theorem continuous_sectionTransition (hn : 1 ≤ n) (τ₁ τ₂ : Section n) :
    Continuous (sectionTransition (R := ℝ) hn τ₁ τ₂) :=
  continuousOn_univ.mp (isPiecewiseAffineOn_sectionTransition hn τ₁ τ₂).continuousOn

/-- `associatorTransition n` over `ℝ` is globally continuous for all `n : ℕ`. -/
theorem continuous_associatorTransition (n : ℕ) :
    Continuous (associatorTransition (R := ℝ) n) :=
  continuousOn_univ.mp (isPiecewiseAffineOn_associatorTransition n).continuousOn

end Excavation

end TauCeti.Hive.Octahedron
