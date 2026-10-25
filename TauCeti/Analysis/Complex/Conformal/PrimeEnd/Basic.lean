/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.PrimeEnd.Crosscut.Basic
public import TauCeti.Topology.Path.Separation
import TauCeti.Topology.ConnectedComponents

/-!
# Null chains and prime ends

Carathéodory's prime ends describe the boundary of a plane domain as seen from inside it. A
**null chain** of `U ⊆ ℂ` is a sequence of crosscuts `C 0, C 1, …` of `U`, each disjoint from the
next, whose chordal diameters tend to zero, and such that the domains they cut off are nested:
the domain `nullChainDomain U C n` of the `n`-th crosscut is the part of `U \ C n` on the side of
`C (n + 1)`, and these domains decrease. Two null chains are equivalent when every domain of
either one contains a domain of the other. A **prime end** of `U` is an equivalence class.

Here the crosscuts of a chain are recorded as sets, the closed ranges of crosscut paths in the
sense of `Path.IsCrosscut`, since every condition depends only on these sets. In particular a
crosscut has two distinct endpoints. Diameters are chordal, measured by
`‖z - w‖ / √((1 + ‖z‖ ^ 2) * (1 + ‖w‖ ^ 2))`, so crosscuts with finite endpoints may run out to
infinity, as the semicircles `|z| = R` of the upper half-plane do as `R → ∞`.

Pommerenke requires instead that each crosscut `C n`, `n ≥ 1`, separates `C 0` from `C (n + 1)`,
and then deduces that the domains are nested from the fact that a crosscut cuts a simply connected
domain into exactly two pieces. Nesting is taken as part of the definition here, and Pommerenke's
separation condition follows from it (`TauCeti.IsNullChain.separatesIn`). Conversely, on a
connected open set separation already forces nesting
(`TauCeti.nullChainDomain_succ_subset_of_separatesIn`), so the two definitions agree there
(`TauCeti.isNullChain_iff_separatesIn`); the two-pieces theorem is not needed for this. On
unbounded domains this definition is narrower than Pommerenke's, whose crosscuts live in the
Riemann sphere and may end at `∞`, while the crosscuts here have finite endpoints. The
nested-domain form makes the equivalence of chains visibly an equivalence relation.

## Main declarations

* `TauCeti.nullChainDomain` -- the domain cut off by the `n`-th crosscut of a chain.
* `IsPreconnected.subset_nullChainDomain` -- a preconnected set off a crosscut that meets its
  domain lies in it.
* `TauCeti.IsNullChain` -- the null-chain predicate.
* `TauCeti.chordal_le_norm_sub`, `TauCeti.norm_sub_le_mul_chordal` -- on a bounded set, chordal
  and Euclidean distances are comparable.
* `TauCeti.IsNullChain.nullChainDomain_eq_connectedComponentIn` -- each domain is the component
  of the cut set containing the next crosscut.
* `TauCeti.IsNullChain.separatesIn` -- Pommerenke's separation condition.
* `TauCeti.nullChainDomain_succ_subset_of_separatesIn`, `TauCeti.isNullChain_iff_separatesIn` --
  conversely, on a connected open set separation forces the domains to be nested, so the two
  definitions of a null chain agree.
* `TauCeti.NullChainEquivalent` -- equivalence of chains, an equivalence relation.
* `TauCeti.PrimeEnd` -- the prime ends of a plane set.
* `TauCeti.PrimeEnd.lift`, `TauCeti.PrimeEnd.ind` -- maps out of prime ends and induction on them.

## References

* Ch. Pommerenke, *Boundary Behaviour of Conformal Maps*, Section 2.4.
* C. Carathéodory, *Über die Begrenzung einfach zusammenhängender Gebiete*, Math. Ann. 73
  (1913).
-/

public section

noncomputable section

open Filter Set Topology

namespace TauCeti

variable {U : Set ℂ} {C C' C'' : ℕ → Set ℂ} {n : ℕ}

/-- The domain cut off by the `n`-th crosscut of a sequence of cuts `C` of `U`: the union of the
connected components of `U \ C n` that meet `C (n + 1)`. For a null chain it is a single
component (`TauCeti.IsNullChain.nullChainDomain_eq_connectedComponentIn`). -/
def nullChainDomain (U : Set ℂ) (C : ℕ → Set ℂ) (n : ℕ) : Set ℂ :=
  ⋃ z ∈ C (n + 1), connectedComponentIn (U \ C n) z

/-- A point lies in the `n`-th domain when it is in the component of `U \ C n` of some point of
`C (n + 1)`. -/
theorem mem_nullChainDomain_iff {z : ℂ} :
    z ∈ nullChainDomain U C n ↔ ∃ w ∈ C (n + 1), z ∈ connectedComponentIn (U \ C n) w := by
  simp [nullChainDomain]

/-- The domain cut off by a crosscut avoids that crosscut. -/
theorem nullChainDomain_subset : nullChainDomain U C n ⊆ U \ C n :=
  iUnion₂_subset fun _ _ => connectedComponentIn_subset _ _

/-- A preconnected subset of `U \ C n` that meets the domain cut off by the `n`-th crosscut lies
in that domain. -/
theorem _root_.IsPreconnected.subset_nullChainDomain {S : Set ℂ} (hS : IsPreconnected S)
    (hSC : S ⊆ U \ C n) (hSD : (S ∩ nullChainDomain U C n).Nonempty) :
    S ⊆ nullChainDomain U C n := by
  obtain ⟨q, hqS, hqD⟩ := hSD
  obtain ⟨w, hw, hqw⟩ := mem_nullChainDomain_iff.mp hqD
  have hSw := hS.subset_connectedComponentIn hqS hSC
  rw [← connectedComponentIn_eq hqw] at hSw
  exact fun z hz => mem_nullChainDomain_iff.mpr ⟨w, hw, hSw hz⟩

/-- If the part of `C (n + 1)` inside `U` is preconnected and misses `C n`, then the domain cut off
by `C n` is the connected component of `U \ C n` containing any point of `C (n + 1)` inside `U`. -/
theorem nullChainDomain_eq_connectedComponentIn_of_isPreconnected
    (hC : IsPreconnected (C (n + 1) ∩ U)) (hdisj : Disjoint (C n) (C (n + 1))) {z : ℂ}
    (hz : z ∈ C (n + 1) ∩ U) :
    nullChainDomain U C n = connectedComponentIn (U \ C n) z := by
  have hsub : C (n + 1) ∩ U ⊆ connectedComponentIn (U \ C n) z :=
    hC.subset_connectedComponentIn hz fun w hw => ⟨hw.2, disjoint_right.mp hdisj hw.1⟩
  refine Subset.antisymm (fun q hq => ?_) fun q hq =>
    mem_nullChainDomain_iff.mpr ⟨z, hz.1, hq⟩
  obtain ⟨w, hw, hqw⟩ := mem_nullChainDomain_iff.mp hq
  have hwU : w ∈ U := (connectedComponentIn_nonempty_iff.mp ⟨q, hqw⟩).1
  rwa [connectedComponentIn_eq (hsub ⟨hw, hwU⟩)]

/-- A **null chain** of `U ⊆ ℂ`: a sequence of crosscuts of `U`, recorded by their closed ranges,
each disjoint from the next, cutting off a decreasing sequence of domains, and with chordal
diameters tending to zero. -/
structure IsNullChain (U : Set ℂ) (C : ℕ → Set ℂ) : Prop where
  /-- Each `C n` is the closed range of a crosscut of `U`. -/
  exists_isCrosscut : ∀ n, ∃ (x y : ℂ) (γ : Path x y), γ.IsCrosscut U ∧ range γ = C n
  /-- Consecutive crosscuts have disjoint closures. -/
  disjoint_succ : ∀ n, Disjoint (C n) (C (n + 1))
  /-- The domains cut off by the crosscuts decrease. -/
  nullChainDomain_succ_subset : ∀ n, nullChainDomain U C (n + 1) ⊆ nullChainDomain U C n
  /-- The chordal diameters of the crosscuts tend to zero. -/
  eventually_chordal_lt : ∀ ε > 0, ∀ᶠ n in atTop, ∀ z ∈ C n, ∀ w ∈ C n,
    ‖z - w‖ / √((1 + ‖z‖ ^ 2) * (1 + ‖w‖ ^ 2)) < ε

/-- The chordal distance is at most the Euclidean distance. -/
theorem chordal_le_norm_sub (z w : ℂ) :
    ‖z - w‖ / √((1 + ‖z‖ ^ 2) * (1 + ‖w‖ ^ 2)) ≤ ‖z - w‖ :=
  div_le_self (norm_nonneg _)
    (Real.one_le_sqrt.mpr (by nlinarith [sq_nonneg ‖z‖, sq_nonneg ‖w‖]))

/-- On the closed disc of radius `R` about `0`, the Euclidean distance is at most `1 + R ^ 2`
times the chordal distance. -/
theorem norm_sub_le_mul_chordal {R : ℝ} {z w : ℂ} (hz : ‖z‖ ≤ R) (hw : ‖w‖ ≤ R) :
    ‖z - w‖ ≤ (1 + R ^ 2) * (‖z - w‖ / √((1 + ‖z‖ ^ 2) * (1 + ‖w‖ ^ 2))) := by
  have hpos : 0 < √((1 + ‖z‖ ^ 2) * (1 + ‖w‖ ^ 2)) := Real.sqrt_pos.mpr (by positivity)
  have hs : √((1 + ‖z‖ ^ 2) * (1 + ‖w‖ ^ 2)) ≤ 1 + R ^ 2 := by
    rw [Real.sqrt_le_left (by positivity)]
    have hz2 : ‖z‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hz 2
    have hw2 : ‖w‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hw 2
    nlinarith [sq_nonneg ‖z‖, sq_nonneg ‖w‖]
  rw [mul_div_assoc', le_div_iff₀ hpos]
  nlinarith [norm_nonneg (z - w)]

namespace IsNullChain

/-- The domains cut off by a null chain decrease. -/
theorem antitone_nullChainDomain (hC : IsNullChain U C) : Antitone (nullChainDomain U C) :=
  antitone_nat_of_succ_le hC.nullChainDomain_succ_subset

/-- The part of a crosscut of a null chain inside the set is connected. -/
theorem isConnected_inter (hC : IsNullChain U C) (n : ℕ) : IsConnected (C n ∩ U) := by
  obtain ⟨x, y, γ, hγ, hrange⟩ := hC.exists_isCrosscut n
  exact hrange ▸ hγ.isConnected_range_inter

/-- The crosscuts of a null chain lie in the closure of the domain. -/
theorem subset_closure (hC : IsNullChain U C) (n : ℕ) : C n ⊆ closure U := by
  obtain ⟨x, y, γ, hγ, hrange⟩ := hC.exists_isCrosscut n
  exact hrange ▸ hγ.range_subset_closure

/-- The next crosscut lies, inside `U`, in the domain cut off by the previous one. -/
theorem inter_subset_nullChainDomain (hC : IsNullChain U C) (n : ℕ) :
    C (n + 1) ∩ U ⊆ nullChainDomain U C n := fun z hz =>
  mem_nullChainDomain_iff.mpr ⟨z, hz.1,
    mem_connectedComponentIn ⟨hz.2, disjoint_right.mp (hC.disjoint_succ n) hz.1⟩⟩

/-- **The domain of a crosscut is a component.** The domain cut off by the `n`-th crosscut of a
null chain is the connected component of `U \ C n` containing any point of `C (n + 1)` inside
`U`. -/
theorem nullChainDomain_eq_connectedComponentIn (hC : IsNullChain U C) {z : ℂ}
    (hz : z ∈ C (n + 1) ∩ U) :
    nullChainDomain U C n = connectedComponentIn (U \ C n) z :=
  nullChainDomain_eq_connectedComponentIn_of_isPreconnected
    (hC.isConnected_inter (n + 1)).isPreconnected (hC.disjoint_succ n) hz

/-- Every domain cut off by a null chain is nonempty. -/
theorem nonempty_nullChainDomain (hC : IsNullChain U C) (n : ℕ) :
    (nullChainDomain U C n).Nonempty :=
  (hC.isConnected_inter (n + 1)).nonempty.mono (hC.inter_subset_nullChainDomain n)

/-- Inside `U`, every crosscut after the first lies in the domain cut off by the first. -/
theorem inter_subset_nullChainDomain_zero (hC : IsNullChain U C) (n : ℕ) :
    C (n + 1) ∩ U ⊆ nullChainDomain U C 0 :=
  (hC.inter_subset_nullChainDomain n).trans (hC.antitone_nullChainDomain (Nat.zero_le n))

/-- **Pommerenke's separation condition.** For a null chain, each crosscut
`C (n + 1)` separates the first crosscut from the next one: their points inside `U` lie in
different components of `U \ C (n + 1)`. -/
theorem separatesIn (hC : IsNullChain U C) {x y : ℂ} {γ : Path x y}
    (hγ : range γ = C (n + 1)) {z w : ℂ} (hz : z ∈ C 0 ∩ U) (hw : w ∈ C (n + 2) ∩ U) :
    γ.SeparatesIn U z w := by
  have h0 : nullChainDomain U C 0 ⊆ U \ C 0 := nullChainDomain_subset
  have hzC : z ∉ C (n + 1) := fun hz' =>
    (h0 (hC.inter_subset_nullChainDomain_zero n ⟨hz', hz.2⟩)).2 hz.1
  have hwD : w ∈ nullChainDomain U C (n + 1) := hC.inter_subset_nullChainDomain (n + 1) hw
  rw [Path.separatesIn_def, hγ]
  refine ⟨⟨hz.2, hzC⟩, nullChainDomain_subset hwD, fun heq => ?_⟩
  have hzD : z ∈ nullChainDomain U C (n + 1) := by
    rw [hC.nullChainDomain_eq_connectedComponentIn hw, heq.symm]
    exact mem_connectedComponentIn ⟨hz.2, hzC⟩
  exact (h0 (hC.antitone_nullChainDomain (Nat.zero_le _) hzD)).2 hz.1

end IsNullChain

/-- **Pommerenke's separation condition forces nesting.** Let `U` be a preconnected open set and
let `C` be a sequence of closed ranges of crosscuts of `U`, each disjoint from the next. If each
crosscut `C (n + 1)` separates the points of the first crosscut inside `U` from those of the next
one, then the domains cut off by `C` decrease. -/
theorem nullChainDomain_succ_subset_of_separatesIn (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hcut : ∀ n, ∃ (x y : ℂ) (γ : Path x y), γ.IsCrosscut U ∧ range γ = C n)
    (hdisj : ∀ n, Disjoint (C n) (C (n + 1)))
    (hsep : ∀ n {x y : ℂ} (γ : Path x y), range γ = C (n + 1) →
      ∀ z ∈ C 0 ∩ U, ∀ w ∈ C (n + 2) ∩ U, γ.SeparatesIn U z w) (n : ℕ) :
    nullChainDomain U C (n + 1) ⊆ nullChainDomain U C n := by
  have hconn (k : ℕ) : IsConnected (C k ∩ U) := by
    obtain ⟨x, y, γ, hγ, hrange⟩ := hcut k
    exact hrange ▸ hγ.isConnected_range_inter
  have hopen (k : ℕ) : IsOpen (U \ C k) := by
    obtain ⟨x, y, γ, -, hrange⟩ := hcut k
    exact hUo.sdiff (hrange ▸ (isCompact_range γ.continuous).isClosed)
  -- Inside `U`, the crosscut `C k` lies in one component of `U \ C j` for any `C j` it misses.
  have hcomp {j k : ℕ} (hjk : Disjoint (C j) (C k)) {v : ℂ} (hv : v ∈ C k ∩ U) :
      C k ∩ U ⊆ connectedComponentIn (U \ C j) v :=
    (hconn k).isPreconnected.subset_connectedComponentIn hv
      fun w hw => ⟨hw.2, disjoint_right.mp hjk hw.1⟩
  have hsep' (k : ℕ) {z w : ℂ} (hz : z ∈ C 0 ∩ U) (hw : w ∈ C (k + 2) ∩ U) :
      z ∈ U \ C (k + 1) ∧ w ∈ U \ C (k + 1) ∧
        connectedComponentIn (U \ C (k + 1)) z ≠ connectedComponentIn (U \ C (k + 1)) w := by
    obtain ⟨x, y, γ, -, hrange⟩ := hcut (k + 1)
    simpa only [Path.separatesIn_def, hrange] using hsep k γ hrange z hz w hw
  obtain ⟨a, ha⟩ := (hconn (n + 1)).nonempty
  obtain ⟨b, hb⟩ := (hconn (n + 2)).nonempty
  obtain ⟨z, hz⟩ := (hconn 0).nonempty
  rw [nullChainDomain_eq_connectedComponentIn_of_isPreconnected (hconn (n + 2)).isPreconnected
      (hdisj (n + 1)) hb,
    nullChainDomain_eq_connectedComponentIn_of_isPreconnected (hconn (n + 1)).isPreconnected
      (hdisj n) ha]
  obtain ⟨hzU, hbU, hzb⟩ := hsep' n hz hb
  -- First, the domain `D` cut off by `C (n + 1)` misses `C n`.
  have hDC : connectedComponentIn (U \ C (n + 1)) b ⊆ U \ C n := by
    intro q hq
    have hqU : q ∈ U := (connectedComponentIn_subset _ _ hq).1
    refine ⟨hqU, fun hqC => ?_⟩
    cases n with
    | zero => exact (hsep' 0 ⟨hqC, hqU⟩ hb).2.2 (connectedComponentIn_eq hq).symm
    | succ m =>
      -- Otherwise `D` contains `C (m + 1) ∩ U`. The component `F` of `U \ C (m + 1)` on the side of
      -- `C 0` is not all of `U`, so its closure meets `C (m + 1) ∩ U ⊆ D`, and `D` meets `F`.
      -- But `F` misses `C (m + 2)`, so it lies on the side of `C 0` of `C (m + 2)`, unlike `D`.
      obtain ⟨hzm, -, hza⟩ := hsep' m hz ha
      have hCD : C (m + 1) ∩ U ⊆ connectedComponentIn (U \ C (m + 1 + 1)) b := by
        rw [connectedComponentIn_eq hq]
        exact hcomp (hdisj (m + 1)).symm ⟨hqC, hqU⟩
      obtain ⟨p, hp, hpF⟩ := hUc.exists_mem_inter_closure_connectedComponentIn_sdiff (hopen (m + 1))
        hzm ha.2 fun h => hza (connectedComponentIn_eq h)
      obtain ⟨y, hyD, hyF⟩ :=
        mem_closure_iff.mp hpF _ (hopen (m + 1 + 1)).connectedComponentIn (hCD hp)
      have hFE : connectedComponentIn (U \ C (m + 1)) z ⊆
          connectedComponentIn (U \ C (m + 1 + 1)) z := by
        refine isPreconnected_connectedComponentIn.subset_connectedComponentIn
          (mem_connectedComponentIn hzm) fun v hv => ⟨(connectedComponentIn_subset _ _ hv).1,
            fun hvC => hza ?_⟩
        rw [connectedComponentIn_eq hv, connectedComponentIn_eq
          (hcomp (hdisj (m + 1)) ha ⟨hvC, (connectedComponentIn_subset _ _ hv).1⟩)]
      exact hzb (by rw [connectedComponentIn_eq (hFE hyF), connectedComponentIn_eq hyD])
  -- Second, the closure of `D` meets `C (n + 1) ∩ U`, which lies in the domain cut off by `C n`.
  obtain ⟨p, hp, hpD⟩ := hUc.exists_mem_inter_closure_connectedComponentIn_sdiff (hopen (n + 1))
    hbU hzU.1 fun h => hzb (connectedComponentIn_eq h).symm
  obtain ⟨y, hya, hyD⟩ :=
    mem_closure_iff.mp hpD _ (hopen n).connectedComponentIn (hcomp (hdisj n) ha hp)
  rw [connectedComponentIn_eq hya]
  exact isPreconnected_connectedComponentIn.subset_connectedComponentIn hyD hDC

/-- **Pommerenke's definition of a null chain.** On a preconnected open set, a sequence of closed
ranges of crosscuts, each disjoint from the next and with chordal diameters tending to zero, is a
null chain exactly when each crosscut `C (n + 1)` separates the points of the first crosscut
inside `U` from those of the next one. -/
theorem isNullChain_iff_separatesIn (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hcut : ∀ n, ∃ (x y : ℂ) (γ : Path x y), γ.IsCrosscut U ∧ range γ = C n)
    (hdisj : ∀ n, Disjoint (C n) (C (n + 1)))
    (hdiam : ∀ ε > 0, ∀ᶠ n in atTop, ∀ z ∈ C n, ∀ w ∈ C n,
      ‖z - w‖ / √((1 + ‖z‖ ^ 2) * (1 + ‖w‖ ^ 2)) < ε) :
    IsNullChain U C ↔ ∀ n {x y : ℂ} (γ : Path x y), range γ = C (n + 1) →
      ∀ z ∈ C 0 ∩ U, ∀ w ∈ C (n + 2) ∩ U, γ.SeparatesIn U z w :=
  ⟨fun hC _ _ _ _ hγ _ hz _ hw => hC.separatesIn hγ hz hw, fun hsep =>
    ⟨hcut, hdisj, nullChainDomain_succ_subset_of_separatesIn hUo hUc hcut hdisj hsep, hdiam⟩⟩

/-- Two sequences of cuts of `U` are **equivalent** when every domain cut off by either one
contains a domain cut off by the other. -/
def NullChainEquivalent (U : Set ℂ) (C C' : ℕ → Set ℂ) : Prop :=
  (∀ m, ∃ n, nullChainDomain U C' n ⊆ nullChainDomain U C m) ∧
    ∀ m, ∃ n, nullChainDomain U C n ⊆ nullChainDomain U C' m

/-- The defining characterization of equivalent chains. -/
theorem nullChainEquivalent_def :
    NullChainEquivalent U C C' ↔
      (∀ m, ∃ n, nullChainDomain U C' n ⊆ nullChainDomain U C m) ∧
        ∀ m, ∃ n, nullChainDomain U C n ⊆ nullChainDomain U C' m :=
  Iff.rfl

@[refl]
theorem NullChainEquivalent.refl (U : Set ℂ) (C : ℕ → Set ℂ) : NullChainEquivalent U C C :=
  ⟨fun m => ⟨m, subset_rfl⟩, fun m => ⟨m, subset_rfl⟩⟩

@[symm]
theorem NullChainEquivalent.symm (h : NullChainEquivalent U C C') : NullChainEquivalent U C' C :=
  ⟨h.2, h.1⟩

@[trans]
theorem NullChainEquivalent.trans (h : NullChainEquivalent U C C')
    (h' : NullChainEquivalent U C' C'') : NullChainEquivalent U C C'' := by
  refine ⟨fun m => ?_, fun m => ?_⟩
  · obtain ⟨k, hk⟩ := h.1 m
    obtain ⟨n, hn⟩ := h'.1 k
    exact ⟨n, hn.trans hk⟩
  · obtain ⟨k, hk⟩ := h'.2 m
    obtain ⟨n, hn⟩ := h.2 k
    exact ⟨n, hn.trans hk⟩

/-- Equivalence of chains is an equivalence relation. -/
theorem equivalence_nullChainEquivalent (U : Set ℂ) : Equivalence (NullChainEquivalent U) :=
  ⟨NullChainEquivalent.refl U, NullChainEquivalent.symm, NullChainEquivalent.trans⟩

/-- Equivalence of null chains of `U`, as a setoid on the null chains. -/
def nullChainSetoid (U : Set ℂ) : Setoid {C : ℕ → Set ℂ // IsNullChain U C} :=
  Setoid.comap Subtype.val ⟨NullChainEquivalent U, equivalence_nullChainEquivalent U⟩

/-- A **prime end** of `U ⊆ ℂ` is an equivalence class of null chains of `U`. -/
def PrimeEnd (U : Set ℂ) : Type :=
  Quotient (nullChainSetoid U)

namespace PrimeEnd

/-- The prime end represented by a null chain. -/
def mk (C : ℕ → Set ℂ) (hC : IsNullChain U C) : PrimeEnd U :=
  Quotient.mk (nullChainSetoid U) ⟨C, hC⟩

/-- Two null chains represent the same prime end exactly when they are equivalent. -/
@[simp]
theorem mk_eq_mk_iff {hC : IsNullChain U C} {hC' : IsNullChain U C'} :
    mk C hC = mk C' hC' ↔ NullChainEquivalent U C C' :=
  Quotient.eq (r := nullChainSetoid U)

/-- Every prime end is represented by a null chain. -/
theorem exists_eq_mk (p : PrimeEnd U) : ∃ (C : ℕ → Set ℂ) (hC : IsNullChain U C), p = mk C hC :=
  Quotient.inductionOn p fun C => ⟨C.1, C.2, rfl⟩

/-- **Induction on prime ends.** To prove a property of every prime end, it suffices to prove it
for the prime end of each null chain. -/
@[elab_as_elim]
theorem ind {motive : PrimeEnd U → Prop} (h : ∀ (C : ℕ → Set ℂ) (hC : IsNullChain U C),
    motive (mk C hC)) (p : PrimeEnd U) : motive p :=
  Quotient.ind (fun C => h C.1 C.2) p

/-- Lift a function on null chains that respects equivalence of chains to a function on prime
ends. -/
def lift {α : Sort*} (f : ∀ C : ℕ → Set ℂ, IsNullChain U C → α)
    (hf : ∀ (C C' : ℕ → Set ℂ) (hC : IsNullChain U C) (hC' : IsNullChain U C'),
      NullChainEquivalent U C C' → f C hC = f C' hC') : PrimeEnd U → α :=
  Quotient.lift (fun C => f C.1 C.2) fun C C' h => hf C.1 C'.1 C.2 C'.2 h

/-- A lifted function evaluates on the prime end of a null chain as on the chain. -/
@[simp]
theorem lift_mk {α : Sort*} (f : ∀ C : ℕ → Set ℂ, IsNullChain U C → α)
    (hf : ∀ (C C' : ℕ → Set ℂ) (hC : IsNullChain U C) (hC' : IsNullChain U C'),
      NullChainEquivalent U C C' → f C hC = f C' hC') (C : ℕ → Set ℂ) (hC : IsNullChain U C) :
    lift f hf (mk C hC) = f C hC := by
  unfold lift mk
  exact Quotient.lift_mk _ _ _

end PrimeEnd

end TauCeti

end
