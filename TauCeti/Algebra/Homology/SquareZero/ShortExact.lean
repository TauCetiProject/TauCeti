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
# Quasi-isomorphisms of quotients by regular chain endomorphisms

Let `(M, d)` and `(N, e)` be abelian groups with square-zero endomorphisms, and let `u` and `v`
be injective endomorphisms of `M` and `N` commuting with `d` and `e`. Suppose that `p : M → P`
and `q : N → Q` are surjections whose kernels are the images of `u` and `v`, intertwining `d`
and `e` with endomorphisms `dP` of `P` and `eQ` of `Q`. Then

`0 → M --u--> M --p--> P → 0` and `0 → N --v--> N --q--> Q → 0`

are short exact sequences of differential groups. A chain map `f : M → N` with `f ∘ u = v ∘ f`,
together with a map `g : P → Q` induced on the quotients (`g ∘ p = q ∘ f`), is a morphism between
them. If `f` induces a bijection on homology, then so does `g`. This is the five lemma for the
long exact homology sequences
`H(M) --u--> H(M) --p--> H(P) --δ--> H(M) --u--> H(M)` and its analogue for `N`.

The statements below give the conclusion in its elementwise form, as for
`LinearMap.homologyMap_surjective_iff` and `LinearMap.homologyMap_injective_iff`: every cycle of
`eQ` differs from the image of a cycle of `dP` by a boundary, and a cycle of `dP` whose image is
a boundary is itself a boundary.

In an abelian category this is `HomologicalComplex.HomologySequence.quasiIso_τ₃`. As in
`Mathlib.Algebra.FiveLemma`, it is reproved here for unbundled maps, by a direct chase on chains
that never constructs the connecting homomorphisms. Only additivity is used, so the maps may be
semilinear over different coefficient rings and the four groups need not be complexes in one
category of modules. This is the situation of the stabilization maps of grid homology, where `u`
and `v` are multiplication by a polynomial variable and `p` and `q` set that variable to zero.

## Main results

* `AddMonoidHom.exists_mem_ker_sub_mem_range_of_exact`: if `f` is surjective on homology, so is
  `g`.
* `AddMonoidHom.mem_range_of_map_mem_range_of_exact`: if `f` is bijective on homology, then `g`
  is injective on homology.
-/

public section

namespace AddMonoidHom

variable {M N P Q : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [AddCommGroup Q]
  {d u : M →+ M} {e v : N →+ N} {dP : P →+ P} {eQ : Q →+ Q} {p : M →+ P} {q : N →+ Q}
  {f : M →+ N}

/-- **Surjectivity on homology passes to quotients by regular endomorphisms.** In a morphism of
short exact sequences `0 → M --u--> M --p--> P → 0` and `0 → N --v--> N --q--> Q → 0` of
differential groups, if every cycle of `e` differs from the image under `f` of a cycle of `d` by
a boundary, and a cycle of `d` whose image under `f` is a boundary is a boundary, then every
cycle of `eQ` differs from the image under `g` of a cycle of `dP` by a boundary. -/
theorem exists_mem_ker_sub_mem_range_of_exact (g : P →+ Q) (he : ∀ n, e (e n) = 0)
    (hdu : ∀ m, d (u m) = u (d m)) (hev : ∀ n, e (v n) = v (e n)) (hv : Function.Injective v)
    (hp : Function.Exact u p) (hq : Function.Exact v q) (hq' : Function.Surjective q)
    (hpd : ∀ m, p (d m) = dP (p m)) (hqe : ∀ n, q (e n) = eQ (q n))
    (hfd : ∀ m, f (d m) = e (f m)) (hfu : ∀ m, f (u m) = v (f m))
    (hgp : ∀ m, g (p m) = q (f m))
    (hsurj : ∀ n ∈ e.ker, ∃ m ∈ d.ker, n - f m ∈ e.range)
    (hinj : ∀ m ∈ d.ker, f m ∈ e.range → m ∈ d.range) {y : Q} (hy : y ∈ eQ.ker) :
    ∃ x ∈ dP.ker, y - g x ∈ eQ.range := by
  obtain ⟨c, rfl⟩ := hq' y
  -- The boundary of a lift `c` of `y` is `v w` for a cycle `w` of `e`.
  obtain ⟨w, hw⟩ := (hq (e c)).mp (by rw [hqe, mem_ker.mp hy])
  have hwe : w ∈ e.ker := mem_ker.mpr <| hv <| by rw [map_zero, ← hev, hw, he]
  obtain ⟨w', hw'd, hww'⟩ := hsurj w hwe
  obtain ⟨b, hb⟩ := mem_range.mp hww'
  -- The cycle `u w'` maps to the boundary of `c - v b`, so it is a boundary `d c'`.
  have hu : u w' ∈ d.ker := mem_ker.mpr <| by rw [hdu, mem_ker.mp hw'd, map_zero]
  obtain ⟨c', hc'⟩ := mem_range.mp <| hinj (u w') hu <| mem_range.mpr
    ⟨c - v b, by rw [map_sub, hev, hb, map_sub, hw, hfu, sub_sub_cancel]⟩
  -- Then `f c' - c + v b` is a cycle of `e`, and `p (c' - y')` is the required cycle of `dP`.
  have hcycle : f c' - c + v b ∈ e.ker := mem_ker.mpr <| by
    rw [map_add, map_sub, ← hfd, hc', hfu, hev, hb, ← hw, map_sub]
    abel
  obtain ⟨y', hy'd, hyy'⟩ := hsurj _ hcycle
  obtain ⟨k, hk⟩ := mem_range.mp hyy'
  refine ⟨p (c' - y'), mem_ker.mpr ?_, mem_range.mpr ⟨-q k, ?_⟩⟩
  · rw [← hpd, map_sub, hc', mem_ker.mp hy'd, sub_zero, hp.apply_apply_eq_zero]
  · simp only [map_neg, ← hqe, hk, hgp, map_sub, map_add, hq.apply_apply_eq_zero]
    abel

/-- **Injectivity on homology passes to quotients by regular endomorphisms.** In a morphism of
short exact sequences `0 → M --u--> M --p--> P → 0` and `0 → N --v--> N --q--> Q → 0` of
differential groups, if every cycle of `e` differs from the image under `f` of a cycle of `d` by
a boundary, and a cycle of `d` whose image under `f` is a boundary is a boundary, then a cycle of
`dP` whose image under `g` is a boundary is a boundary. -/
theorem mem_range_of_map_mem_range_of_exact (g : P →+ Q) (hd : ∀ m, d (d m) = 0)
    (he : ∀ n, e (e n) = 0) (hdu : ∀ m, d (u m) = u (d m)) (hev : ∀ n, e (v n) = v (e n))
    (hu : Function.Injective u) (hv : Function.Injective v) (hp : Function.Exact u p)
    (hp' : Function.Surjective p) (hq : Function.Exact v q) (hq' : Function.Surjective q)
    (hpd : ∀ m, p (d m) = dP (p m)) (hqe : ∀ n, q (e n) = eQ (q n))
    (hfd : ∀ m, f (d m) = e (f m)) (hfu : ∀ m, f (u m) = v (f m))
    (hgp : ∀ m, g (p m) = q (f m))
    (hsurj : ∀ n ∈ e.ker, ∃ m ∈ d.ker, n - f m ∈ e.range)
    (hinj : ∀ m ∈ d.ker, f m ∈ e.range → m ∈ d.range) {x : P} (hx : x ∈ dP.ker)
    (hgx : g x ∈ eQ.range) : x ∈ dP.range := by
  obtain ⟨c, rfl⟩ := hp' x
  -- The boundary of a lift `c` of `x` is `u w` for a cycle `w` of `d`.
  obtain ⟨w, hw⟩ := (hp (d c)).mp (by rw [hpd, mem_ker.mp hx])
  have hwd : w ∈ d.ker := mem_ker.mpr <| hu <| by rw [map_zero, ← hdu, hw, hd]
  obtain ⟨b, hb⟩ := mem_range.mp hgx
  obtain ⟨b, rfl⟩ := hq' b
  -- Lifting `g x = eQ (q b)` shows `f c = e b + v a`, where `e a = f w`.
  obtain ⟨a, ha⟩ := (hq (f c - e b)).mp (by rw [map_sub, hqe, hb, hgp, sub_self])
  have hea : e a = f w := hv <| by rw [← hev, ha, map_sub, ← hfd, ← hw, hfu, he, sub_zero]
  -- So `f w` is a boundary, hence `w = d a'` and `c - u a'` is a cycle of `d`.
  obtain ⟨a', ha'⟩ := mem_range.mp <| hinj w hwd <| mem_range.mpr ⟨a, hea⟩
  have hcycle : a - f a' ∈ e.ker := mem_ker.mpr <| by rw [map_sub, hea, ← hfd, ha', sub_self]
  -- Correcting `c - u a'` by `u h` for a cycle `h` makes its image a boundary.
  obtain ⟨h, hhd, hah⟩ := hsurj _ hcycle
  obtain ⟨k, hk⟩ := mem_range.mp hah
  obtain ⟨m, hm⟩ := mem_range.mp <| hinj (c - u a' - u h)
    (mem_ker.mpr <| by rw [map_sub, map_sub, hdu, hdu, ha', hw, mem_ker.mp hhd, map_zero,
      sub_self, sub_zero])
    (mem_range.mpr ⟨b + v k, by
      simp only [map_add, map_sub, hev, hk, hfu, ha]
      abel⟩)
  refine mem_range.mpr ⟨p m, ?_⟩
  rw [← hpd, hm, map_sub, map_sub, hp.apply_apply_eq_zero, hp.apply_apply_eq_zero, sub_zero,
    sub_zero]

end AddMonoidHom
