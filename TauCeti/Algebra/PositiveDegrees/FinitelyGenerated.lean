/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Group.Submonoid.PositiveDegree
public import TauCeti.Algebra.PositiveDegrees.Map

/-!
# Positive degrees from finite generation

A strictly positive integral functional on a finitely generated additive submonoid gives positive
degree data: the finite cutoffs are supplied by `AddSubmonoid.FG.finite_degree_le`. Likewise,
an additive map between finitely generated positive degree data which is nonzero on nonzero allowed
degrees is a positive degree map with a linear cutoff modulus, by
`AddSubmonoid.FG.exists_degree_le_mul`.

## Main declarations

* `TauCeti.PositiveDegrees.ofFG`: positive degree data from a finitely generated submonoid and a
  strictly positive integral functional.
* `TauCeti.PositiveDegreeMap.ofFG`: the positive degree map of an additive map nonzero on nonzero
  allowed degrees out of finitely generated positive degree data.

Adapted from `Mei/Algebra/PositiveDegrees/FinitelyGenerated.lean` and `Map.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`3d2e9c869ee44c41ae9c7b5c6e2042898430d0ca`, released under Apache 2.0.
-/

public section

namespace TauCeti

variable {N M : Type*} [AddCommMonoid N] [AddCommMonoid M]

namespace PositiveDegrees

/-- A strictly positive integral functional on a finitely generated submonoid defines positive
degree data, without a cancellation or saturation assumption. -/
def ofFG {P : AddSubmonoid N} (hP : P.FG) (δ : N →+ ℤ)
    (hδ : ∀ {n}, n ∈ P → n ≠ 0 → 0 < δ n) : PositiveDegrees N where
  monoid := P
  degree := δ
  degree_pos := hδ
  finite_le := hP.finite_degree_le δ (fun _ hn hn0 => hδ hn hn0)

/-- The finite-generation construction retains the given submonoid. -/
@[simp]
theorem ofFG_monoid {P : AddSubmonoid N} (hP : P.FG) (δ : N →+ ℤ)
    (hδ : ∀ {n}, n ∈ P → n ≠ 0 → 0 < δ n) :
    (ofFG hP δ hδ).monoid = P := (rfl)

/-- The finite-generation construction retains the given functional. -/
@[simp]
theorem ofFG_degree {P : AddSubmonoid N} (hP : P.FG) (δ : N →+ ℤ)
    (hδ : ∀ {n}, n ∈ P → n ≠ 0 → 0 < δ n) :
    (ofFG hP δ hδ).degree = δ := (rfl)

end PositiveDegrees

namespace PositiveDegreeMap

variable {d : PositiveDegrees N} {e : PositiveDegrees M}

/-- An additive map which sends allowed degrees to allowed degrees and nonzero allowed degrees to
nonzero elements has a linear cutoff modulus when the source monoid is finitely generated. No
injectivity of the additive map is needed. -/
noncomputable def ofFG (T : N →+ M) (hmem : ∀ n ∈ d.monoid, T n ∈ e.monoid)
    (hne : ∀ n ∈ d.monoid, n ≠ 0 → T n ≠ 0) (hfg : d.monoid.FG) :
    PositiveDegreeMap d e :=
  ofBound T hmem
    (hfg.exists_degree_le_mul d.degree (e.degree.comp T)
      (fun n hn hn0 => e.degree_pos (hmem n hn) (hne n hn hn0))).choose
    (hfg.exists_degree_le_mul d.degree (e.degree.comp T)
      (fun n hn hn0 => e.degree_pos (hmem n hn) (hne n hn hn0))).choose_spec

/-- The finitely generated construction is the given additive map. -/
@[simp]
theorem ofFG_apply (T : N →+ M) (hmem : ∀ n ∈ d.monoid, T n ∈ e.monoid)
    (hne : ∀ n ∈ d.monoid, n ≠ 0 → T n ≠ 0) (hfg : d.monoid.FG) (n : N) :
    ofFG (d := d) (e := e) T hmem hne hfg n = T n :=
  ofBound_apply (d := d) (e := e) T _ _ _ n

/-- The finitely generated construction has a linear modulus. -/
theorem exists_ofFG_modulus_eq_mul (T : N →+ M) (hmem : ∀ n ∈ d.monoid, T n ∈ e.monoid)
    (hne : ∀ n ∈ d.monoid, n ≠ 0 → T n ≠ 0) (hfg : d.monoid.FG) :
    ∃ c : ℕ, ∀ k, (ofFG (d := d) (e := e) T hmem hne hfg).modulus k = c * k :=
  ⟨_, fun k => ofBound_modulus (d := d) (e := e) T _ _ _ k⟩

end PositiveDegreeMap

end TauCeti
