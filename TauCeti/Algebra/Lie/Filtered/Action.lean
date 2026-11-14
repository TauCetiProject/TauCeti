/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Lie.Graded.Truncation
public import TauCeti.LinearAlgebra.Submodule.CompleteFiltration

/-!
# Finite-order filtration-raising Lie actions

A filtration-raising action of a positively graded Lie algebra on a filtered module descends
to the finite-order coefficient modules for any decreasing coefficient filtration, and the
quotient transitions intertwine the actions. If `F 0 = ⊤`, the order-`k` action also factors
through the order-`k` Lie truncation and every acting endomorphism has `(k + 1)`st power zero.
These are the finite-order representations needed for exponentiating actions on completed
coefficient modules.

The quotient representation uses Mathlib's `LieSubmodule.Quotient.actionAsEndoMap`.
Nilpotence uses Mathlib's `Submodule.mapQ_pow` and the existing
`Module.End.pow_apply_mem_of_map_le`. The coefficient filtration is an arbitrary
decreasing family of submodules, as used by `ModuleTower.quotients`. The adjoint
action is filtration-raising for its
own degree filtration. No freeness, separatedness, finite-dimensionality,
or characteristic-zero assumption is needed.

Adapted from `Mei/Algebra/Lie/Filtered/Action.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`a79c57178cc83666fc244ca6e6eeaa722e9b8bc7` (Apache 2.0).
-/

public section

attribute [local instance] LieRing.ofAssociativeRing

namespace TauCeti

variable {N R L M : Type*} [AddCommMonoid N] [CommRing R]
  [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M]
  [LieRingModule L M]

/-- An action raises filtration orders when Lie terms of degree at least `a + 1` send
module terms of order `b` into order `a + b + 1`. The successor convention agrees with
`PositiveDegrees.degreeSubmodule`, which consists of Lie degrees strictly above its cutoff. -/
class IsFiltrationRaising (d : PositiveDegrees N) (ℒ : N → Submodule R L)
    (F : ℕ → Submodule R M) : Prop where
  /-- Lie and module filtration orders add under the action. -/
  lie_mem : ∀ {a b : ℕ} {x : L} {m : M},
    x ∈ d.degreeSubmodule ℒ a → m ∈ F b →
      ⁅x, m⁆ ∈ F (a + b + 1)

/-- Restricting a filtration-raising action to a Lie subalgebra preserves the
filtration bound for the inverse-image homogeneous pieces. -/
instance IsFiltrationRaising.lieSubalgebra (d : PositiveDegrees N)
    (ℒ : N → Submodule R L) (F : ℕ → Submodule R M)
    [IsFiltrationRaising d ℒ F] (K : LieSubalgebra R L) :
    IsFiltrationRaising d (fun n => (ℒ n).comap K.incl.toLinearMap) F where
  lie_mem {a b x m} hx hm := by
    have hle : d.degreeSubmodule (fun n => (ℒ n).comap K.incl.toLinearMap) a ≤
        (d.degreeSubmodule ℒ a).comap K.incl.toLinearMap := by
      rw [d.degreeSubmodule_def]
      exact iSup_le fun n => Submodule.comap_mono (d.le_degreeSubmodule ℒ n.property)
    exact IsFiltrationRaising.lie_mem (d := d) (ℒ := ℒ) (F := F) (hle hx) hm

/-- Bracketing raises the degree filtration on the Lie algebra itself. At positive
order `b`, the family retains degrees at least `b`. For a positive grading its
zeroth term is the whole algebra. -/
instance IsFiltrationRaising.adjoint (d : PositiveDegrees N) (ℒ : N → Submodule R L)
    [SetLike.GradedBracket ℒ ℒ] :
    IsFiltrationRaising d ℒ (fun b => d.degreeSubmodule ℒ (b - 1)) where
  lie_mem {a b x y} hx hy :=
    d.degreeSubmodule_antitone ℒ (by omega : a + b ≤ a + (b - 1) + 1)
      (d.lie_mem_degreeSubmodule ℒ hx hy)

namespace PositiveDegrees

variable (d : PositiveDegrees N) (ℒ : N → Submodule R L)
  (F : ℕ → Submodule R M) (hF : Antitone F)

section Module

variable [DecidableEq N] [DirectSum.Decomposition ℒ] [IsPositiveGrading d ℒ]
  [IsFiltrationRaising d ℒ F]

include d ℒ

omit [DecidableEq N] [DirectSum.Decomposition ℒ] in
/-- A homogeneous Lie element raises coefficient order by its integral degree. -/
theorem lie_mem_of_mem_homogeneous
    {n : N} {x : L} (hx : x ∈ ℒ n) {b : ℕ} {m : M} (hm : m ∈ F b) :
    ⁅x, m⁆ ∈ F ((d.degree n).toNat + b) := by
  by_cases hn : 0 < d.degree n
  · have hx' : x ∈ d.degreeSubmodule ℒ ((d.degree n).toNat - 1) :=
      d.le_degreeSubmodule ℒ (by omega) hx
    have h := IsFiltrationRaising.lie_mem (d := d) (ℒ := ℒ) (F := F) hx' hm
    have he : (d.degree n).toNat - 1 + b + 1 = (d.degree n).toNat + b := by omega
    exact he ▸ h
  · have hx0 : x = 0 := by
      simpa only [d.eq_bot_of_degree_nonpos ℒ n (by omega), Submodule.mem_bot] using hx
    simp [hx0]

/-- Every Lie element raises the module filtration by at least one. -/
theorem lie_mem_succ (x : L) {b : ℕ} {m : M} (hm : m ∈ F b) :
    ⁅x, m⁆ ∈ F (b + 1) := by
  simpa only [Nat.zero_add] using
    IsFiltrationRaising.lie_mem (d := d) (ℒ := ℒ) (F := F)
      (by simp : x ∈ d.degreeSubmodule ℒ 0) hm

/-- Every filtration term is a Lie submodule for a filtration-raising action. -/
def filtrationLieSubmodule (b : ℕ) : LieSubmodule R L M where
  toSubmodule := F b
  lie_mem := fun {x _} hm => hF (Nat.le_succ b) (d.lie_mem_succ ℒ F x hm)

/-- Passing to the stable Lie submodule preserves the original filtration term. -/
@[simp]
theorem filtrationLieSubmodule_toSubmodule (b : ℕ) :
    (d.filtrationLieSubmodule ℒ F hF b).toSubmodule = F b := (rfl)

/-- Membership in a stable Lie submodule is membership in the original filtration term. -/
@[simp]
theorem mem_filtrationLieSubmodule {b : ℕ} {m : M} :
    m ∈ d.filtrationLieSubmodule ℒ F hF b ↔ m ∈ F b := (Iff.rfl)

variable [LieModule R L M]

/-- The representation on the module retaining coefficient orders at most `k`. -/
def quotientLieAction (k : ℕ) : L →ₗ⁅R⁆ Module.End R (M ⧸ F (k + 1)) :=
  LieSubmodule.Quotient.actionAsEndoMap (d.filtrationLieSubmodule ℒ F hF (k + 1))

/-- On representatives, the quotient representation is the original Lie action. -/
@[simp]
theorem quotientLieAction_mk (k : ℕ) (x : L) (m : M) :
    d.quotientLieAction ℒ F hF k x (Submodule.Quotient.mk m) =
      Submodule.Quotient.mk ⁅x, m⁆ := (rfl)

/-- At order `k`, the `(k + 1)`st power of every acting endomorphism vanishes. -/
@[simp]
theorem quotientLieAction_pow_eq_zero (hF0 : F 0 = ⊤) (k : ℕ) (x : L) :
    d.quotientLieAction ℒ F hF k x ^ (k + 1) = 0 := by
  let f := LieModule.toEnd R L M x
  have hf : ∀ b, F b ≤ (F (b + 1)).comap f := fun b _ hm => d.lie_mem_succ ℒ F x hm
  have hp : F (k + 1) ≤ (F (k + 1)).comap f :=
    fun _ hm => hF (Nat.le_succ (k + 1)) (hf (k + 1) hm)
  have he : d.quotientLieAction ℒ F hF k x = (F (k + 1)).mapQ (F (k + 1)) f hp := by
    ext m
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply,
      quotientLieAction_mk, Submodule.mapQ_apply, f, LieModule.toEnd_apply_apply]
  rw [he, ← Submodule.mapQ_pow]
  ext m
  rw [LinearMap.comp_apply, LinearMap.comp_apply, Submodule.mkQ_apply,
    Submodule.mapQ_apply, LinearMap.zero_apply, Submodule.Quotient.mk_eq_zero]
  simpa only [Nat.zero_add] using
    Module.End.pow_apply_mem_of_map_le
      (fun b => Submodule.map_le_iff_le_comap.mpr (hf b))
      (by simp [hF0] : m ∈ F 0) (k + 1)

/-- Every finite-order acting endomorphism is nilpotent, over any commutative ring. -/
theorem isNilpotent_quotientLieAction (hF0 : F 0 = ⊤) (k : ℕ) (x : L) :
    IsNilpotent (d.quotientLieAction ℒ F hF k x) :=
  ⟨k + 1, d.quotientLieAction_pow_eq_zero ℒ F hF hF0 k x⟩

/-- Coefficient transitions intertwine the finite-order representations. -/
@[simp]
theorem factor_quotientLieAction {k l : ℕ} (h : k ≤ l) (x : L) (q : M ⧸ F (l + 1)) :
    Submodule.factor (hF (Nat.add_le_add_right h 1)) (d.quotientLieAction ℒ F hF l x q) =
      d.quotientLieAction ℒ F hF k x (Submodule.factor (hF (Nat.add_le_add_right h 1)) q) := by
  induction q using Submodule.Quotient.induction_on with
  | _ m =>
    simp only [Submodule.factor, Submodule.mapQ_apply, LinearMap.id_apply, quotientLieAction_mk]

section EquivariantMap

variable {M' : Type*} [AddCommGroup M'] [Module R M']
  [LieRingModule L M'] [LieModule R L M']
  (G : ℕ → Submodule R M') (hG : Antitone G) [IsFiltrationRaising d ℒ G]
  (f : M →ₗ[R] M') (hf : ∀ (x : L) (m : M), f ⁅x, m⁆ = ⁅x, f m⁆)

include hf

/-- An equivariant coefficient map intertwines the finite-order actions whenever
it descends to the chosen pair of coefficient quotients. -/
theorem mapQ_quotientLieAction {l k : ℕ}
    (h : F (l + 1) ≤ (G (k + 1)).comap f) (x : L) (q : M ⧸ F (l + 1)) :
    (F (l + 1)).mapQ (G (k + 1)) f h (d.quotientLieAction ℒ F hF l x q) =
      d.quotientLieAction ℒ G hG k x ((F (l + 1)).mapQ (G (k + 1)) f h q) := by
  induction q using Submodule.Quotient.induction_on with
  | _ m => simp only [quotientLieAction_mk, Submodule.mapQ_apply, hf]

end EquivariantMap

end Module

section Lie

variable (hF0 : F 0 = ⊤)

include hF0

variable [LieModule R L M] [DecidableEq N] [GradedLieAlgebra ℒ]
  [IsPositiveGrading d ℒ] [IsFiltrationRaising d ℒ F]

/-- Lie terms above order `k` act trivially on the order-`k` coefficient module. -/
theorem degreeIdeal_le_ker_quotientLieAction (k : ℕ) :
    d.degreeIdeal ℒ k ≤ (d.quotientLieAction ℒ F hF k).ker := by
  intro x hx
  rw [LieHom.mem_ker]
  apply LinearMap.ext
  intro q
  obtain ⟨m, rfl⟩ := (F (k + 1)).mkQ_surjective q
  rw [Submodule.mkQ_apply, quotientLieAction_mk, LinearMap.zero_apply,
    Submodule.Quotient.mk_eq_zero]
  have hx' : x ∈ d.degreeSubmodule ℒ k := by
    rw [← d.degreeIdeal_toSubmodule ℒ k]
    exact hx
  simpa only [Nat.add_zero] using
    IsFiltrationRaising.lie_mem (d := d) (ℒ := ℒ) (F := F) hx'
      (by simp [hF0] : m ∈ F 0)

/-- The action of the order-`k` Lie truncation on the order-`k` coefficient module. -/
def truncatedLieAction (k : ℕ) :
    d.truncatedLie ℒ k →ₗ⁅R⁆ Module.End R (M ⧸ F (k + 1)) :=
  (d.degreeIdeal ℒ k).liftQ (d.quotientLieAction ℒ F hF k)
    (d.degreeIdeal_le_ker_quotientLieAction ℒ F hF hF0 k)

/-- The truncated representation agrees with the quotient action on Lie representatives. -/
@[simp]
theorem truncatedLieAction_mk (k : ℕ) (x : L) :
    d.truncatedLieAction ℒ F hF hF0 k (LieSubmodule.Quotient.mk x) =
      d.quotientLieAction ℒ F hF k x := by
  simp [truncatedLieAction]

/-- The nilpotence bound holds for arbitrary elements of the Lie truncation. -/
@[simp]
theorem truncatedLieAction_pow_eq_zero (k : ℕ) (x : d.truncatedLie ℒ k) :
    d.truncatedLieAction ℒ F hF hF0 k x ^ (k + 1) = 0 := by
  obtain ⟨x, rfl⟩ := (d.degreeIdeal ℒ k).surjective_mkQ x
  rw [LieIdeal.mkQ_apply, truncatedLieAction_mk]
  exact d.quotientLieAction_pow_eq_zero ℒ F hF hF0 k x

/-- Lie and coefficient truncations commute with their finite-order actions. -/
@[simp]
theorem factor_truncatedLieAction {k l : ℕ} (h : k ≤ l)
    (x : d.truncatedLie ℒ l) (q : M ⧸ F (l + 1)) :
    Submodule.factor (hF (Nat.add_le_add_right h 1)) (d.truncatedLieAction ℒ F hF hF0 l x q) =
      d.truncatedLieAction ℒ F hF hF0 k (d.truncationMap ℒ h x)
        (Submodule.factor (hF (Nat.add_le_add_right h 1)) q) := by
  obtain ⟨x, rfl⟩ := (d.degreeIdeal ℒ l).surjective_mkQ x
  simp only [LieIdeal.mkQ_apply, truncatedLieAction_mk, PositiveDegrees.truncationMap_mk]
  exact d.factor_quotientLieAction ℒ F hF h x q

end Lie

end PositiveDegrees
end TauCeti
