/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Tactic.Abel

/-!
# The five lemma for short exact sequences of differential groups

A short exact sequence of differential groups `0 → M₁ --u--> M --p--> P → 0` consists of abelian
groups with endomorphisms `d₁`, `d` and `dP`, where `d` squares to zero, `u` is injective, `p` is
surjective, the kernel of `p` is the image of `u`, and `u` and `p` intertwine the differentials
(`AddMonoidHom.IsShortExactDifferential`). Given a second such sequence
`0 → N₁ --v--> N --q--> Q → 0`, maps `f₁ : M₁ → N₁`, `f : M → N` and `g : P → Q` with
`f ∘ u = v ∘ f₁` and `g ∘ p = q ∘ f` form a morphism of short exact sequences. The five lemma for
the long exact homology sequences
`H(M₁) --u--> H(M) --p--> H(P) --δ--> H(M₁) --u--> H(M)` and its analogue for `N` transfers
surjectivity and injectivity on homology from `f₁` and `f` to `g`.

The statements below give the conclusion in its elementwise form, as for
`LinearMap.homologyMap_surjective_iff` and `LinearMap.homologyMap_injective_iff`: every cycle of
`eQ` differs from the image of a cycle of `dP` by a boundary, and a cycle of `dP` whose image is
a boundary is itself a boundary.

In an abelian category this is `HomologicalComplex.HomologySequence.quasiIso_τ₃`. As in
`Mathlib.Algebra.FiveLemma`, it is reproved here for unbundled maps, by a direct chase on chains
that never constructs the connecting homomorphisms. Only additivity is used, so the maps may be
semilinear over different coefficient rings and the groups need not be complexes in one
category of modules. This is the situation of the stabilization maps of grid homology, where `u`
and `v` are multiplication by a polynomial variable and `p` and `q` set that variable to zero.

## Main definitions

* `AddMonoidHom.IsShortExactDifferential`: `0 → M₁ --u--> M --p--> P → 0` is a short exact
  sequence of differential groups.

## Main results

* `AddMonoidHom.exists_mem_ker_sub_mem_range_of_exact`: if `f₁` is surjective on homology and
  `f` is bijective on homology, then `g` is surjective on homology.
* `AddMonoidHom.mem_range_of_map_mem_range_of_exact`: if `f₁` is bijective on homology and `f`
  is injective on homology, then `g` is injective on homology.
-/

public section

namespace AddMonoidHom

variable {M₁ M P N₁ N Q : Type*} [AddCommGroup M₁] [AddCommGroup M] [AddCommGroup P]
  [AddCommGroup N₁] [AddCommGroup N] [AddCommGroup Q]

/-- `0 → M₁ --u--> M --p--> P → 0` is a short exact sequence of differential groups with
differentials `d₁`, `d` and `dP`: the middle differential `d` squares to zero, `u` is injective,
`p` is surjective with kernel the image of `u`, and `u` and `p` commute with the differentials. -/
structure IsShortExactDifferential (u : M₁ →+ M) (p : M →+ P) (d₁ : M₁ →+ M₁) (d : M →+ M)
    (dP : P →+ P) : Prop where
  /-- The middle differential squares to zero. -/
  square_zero : ∀ m, d (d m) = 0
  /-- The left map is injective. -/
  injective : Function.Injective u
  /-- The kernel of the right map is the image of the left map. -/
  exact : Function.Exact u p
  /-- The right map is surjective. -/
  surjective : Function.Surjective p
  /-- The left map is a chain map. -/
  comm_left : ∀ m, d (u m) = u (d₁ m)
  /-- The right map is a chain map. -/
  comm_right : ∀ m, p (d m) = dP (p m)

variable {d₁ : M₁ →+ M₁} {d : M →+ M} {dP : P →+ P} {e₁ : N₁ →+ N₁} {e : N →+ N} {eQ : Q →+ Q}
  {u : M₁ →+ M} {p : M →+ P} {v : N₁ →+ N} {q : N →+ Q} {f₁ : M₁ →+ N₁} {f : M →+ N}

/-- **Five lemma, surjectivity on homology.** In a morphism `(f₁, f, g)` of short exact sequences
`0 → M₁ --u--> M --p--> P → 0` and `0 → N₁ --v--> N --q--> Q → 0` of differential groups, suppose
that every cycle of `e₁` differs from the image under `f₁` of a cycle of `d₁` by a boundary, that
every cycle of `e` differs from the image under `f` of a cycle of `d` by a boundary, and that a
cycle of `d` whose image under `f` is a boundary is a boundary. Then every cycle of `eQ` differs
from the image under `g` of a cycle of `dP` by a boundary. -/
theorem exists_mem_ker_sub_mem_range_of_exact (g : P →+ Q)
    (hM : u.IsShortExactDifferential p d₁ d dP) (hN : v.IsShortExactDifferential q e₁ e eQ)
    (hfd : ∀ m, f (d m) = e (f m)) (hfu : ∀ m, f (u m) = v (f₁ m))
    (hgp : ∀ m, g (p m) = q (f m))
    (hsurj₁ : ∀ n ∈ e₁.ker, ∃ m ∈ d₁.ker, n - f₁ m ∈ e₁.range)
    (hsurj : ∀ n ∈ e.ker, ∃ m ∈ d.ker, n - f m ∈ e.range)
    (hinj : ∀ m ∈ d.ker, f m ∈ e.range → m ∈ d.range) {y : Q} (hy : y ∈ eQ.ker) :
    ∃ x ∈ dP.ker, y - g x ∈ eQ.range := by
  obtain ⟨c, rfl⟩ := hN.surjective y
  -- The boundary of a lift `c` of `y` is `v w` for a cycle `w` of `e₁`.
  obtain ⟨w, hw⟩ := (hN.exact (e c)).mp (by rw [hN.comm_right, mem_ker.mp hy])
  have hwe : w ∈ e₁.ker := mem_ker.mpr <| hN.injective <| by
    rw [map_zero, ← hN.comm_left, hw, hN.square_zero]
  obtain ⟨w', hw'd, hww'⟩ := hsurj₁ w hwe
  obtain ⟨b, hb⟩ := mem_range.mp hww'
  -- The cycle `u w'` maps to the boundary of `c - v b`, so it is a boundary `d c'`.
  have hu : u w' ∈ d.ker := mem_ker.mpr <| by rw [hM.comm_left, mem_ker.mp hw'd, map_zero]
  obtain ⟨c', hc'⟩ := mem_range.mp <| hinj (u w') hu <| mem_range.mpr
    ⟨c - v b, by rw [map_sub, hN.comm_left, hb, map_sub, hw, hfu, sub_sub_cancel]⟩
  -- Then `f c' - c + v b` is a cycle of `e`, and `p (c' - y')` is the required cycle of `dP`.
  have hcycle : f c' - c + v b ∈ e.ker := mem_ker.mpr <| by
    rw [map_add, map_sub, ← hfd, hc', hfu, hN.comm_left, hb, ← hw, map_sub]
    abel
  obtain ⟨y', hy'd, hyy'⟩ := hsurj _ hcycle
  obtain ⟨k, hk⟩ := mem_range.mp hyy'
  refine ⟨p (c' - y'), mem_ker.mpr ?_, mem_range.mpr ⟨-q k, ?_⟩⟩
  · rw [← hM.comm_right, map_sub, hc', mem_ker.mp hy'd, sub_zero, hM.exact.apply_apply_eq_zero]
  · simp only [map_neg, ← hN.comm_right, hk, hgp, map_sub, map_add, hN.exact.apply_apply_eq_zero]
    abel

/-- **Five lemma, injectivity on homology.** In a morphism `(f₁, f, g)` of short exact sequences
`0 → M₁ --u--> M --p--> P → 0` and `0 → N₁ --v--> N --q--> Q → 0` of differential groups, suppose
that every cycle of `e₁` differs from the image under `f₁` of a cycle of `d₁` by a boundary, and
that a cycle of `d₁` or of `d` whose image under `f₁` or `f` is a boundary is a boundary. Then a
cycle of `dP` whose image under `g` is a boundary is a boundary. -/
theorem mem_range_of_map_mem_range_of_exact (g : P →+ Q)
    (hM : u.IsShortExactDifferential p d₁ d dP) (hN : v.IsShortExactDifferential q e₁ e eQ)
    (hf₁d : ∀ m, f₁ (d₁ m) = e₁ (f₁ m)) (hfd : ∀ m, f (d m) = e (f m))
    (hfu : ∀ m, f (u m) = v (f₁ m)) (hgp : ∀ m, g (p m) = q (f m))
    (hsurj₁ : ∀ n ∈ e₁.ker, ∃ m ∈ d₁.ker, n - f₁ m ∈ e₁.range)
    (hinj₁ : ∀ m ∈ d₁.ker, f₁ m ∈ e₁.range → m ∈ d₁.range)
    (hinj : ∀ m ∈ d.ker, f m ∈ e.range → m ∈ d.range) {x : P} (hx : x ∈ dP.ker)
    (hgx : g x ∈ eQ.range) : x ∈ dP.range := by
  obtain ⟨c, rfl⟩ := hM.surjective x
  -- The boundary of a lift `c` of `x` is `u w` for a cycle `w` of `d₁`.
  obtain ⟨w, hw⟩ := (hM.exact (d c)).mp (by rw [hM.comm_right, mem_ker.mp hx])
  have hwd : w ∈ d₁.ker := mem_ker.mpr <| hM.injective <| by
    rw [map_zero, ← hM.comm_left, hw, hM.square_zero]
  obtain ⟨b, hb⟩ := mem_range.mp hgx
  obtain ⟨b, rfl⟩ := hN.surjective b
  -- Lifting `g x = eQ (q b)` shows `f c = e b + v a`, where `e₁ a = f₁ w`.
  obtain ⟨a, ha⟩ := (hN.exact (f c - e b)).mp (by rw [map_sub, hN.comm_right, hb, hgp, sub_self])
  have hea : e₁ a = f₁ w := hN.injective <| by
    rw [← hN.comm_left, ha, map_sub, ← hfd, ← hw, hfu, hN.square_zero, sub_zero]
  -- So `f₁ w` is a boundary, hence `w = d₁ a'` and `a - f₁ a'` is a cycle of `e₁`.
  obtain ⟨a', ha'⟩ := mem_range.mp <| hinj₁ w hwd <| mem_range.mpr ⟨a, hea⟩
  have hcycle : a - f₁ a' ∈ e₁.ker := mem_ker.mpr <| by
    rw [map_sub, hea, ← hf₁d, ha', sub_self]
  -- Correcting `c - u a'` by `u h` for a cycle `h` makes its image a boundary.
  obtain ⟨h, hhd, hah⟩ := hsurj₁ _ hcycle
  obtain ⟨k, hk⟩ := mem_range.mp hah
  obtain ⟨m, hm⟩ := mem_range.mp <| hinj (c - u a' - u h)
    (mem_ker.mpr <| by rw [map_sub, map_sub, hM.comm_left, hM.comm_left, ha', hw,
      mem_ker.mp hhd, map_zero, sub_self, sub_zero])
    (mem_range.mpr ⟨b + v k, by
      simp only [map_add, map_sub, hN.comm_left, hk, hfu, ha]
      abel⟩)
  refine mem_range.mpr ⟨p m, ?_⟩
  rw [← hM.comm_right, hm, map_sub, map_sub, hM.exact.apply_apply_eq_zero,
    hM.exact.apply_apply_eq_zero, sub_zero, sub_zero]

end AddMonoidHom
