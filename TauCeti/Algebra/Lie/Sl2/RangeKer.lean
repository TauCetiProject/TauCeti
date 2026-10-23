/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Sl2.Morozov
public import TauCeti.RepresentationTheory.Lie.AdNilpotent
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The range of the raising operator is complementary to the kernel of the lowering operator

Let `t : IsSl2Triple h e f` be an `sl₂` triple in a Lie algebra `L` over a field `K` of
characteristic zero, and let `M` be a finite-dimensional `L`-module. This file proves the
decomposition

`M = e • M ⊕ ker f`.

The kernel of `f` consists of the lowest weight vectors. In the decomposition of `M` into
irreducible `V(n)`s, each summand contributes one lowest weight line, and the rest of the summand
is the image of the raising operator. The proof here does not use that decomposition, a splitting
field or the diagonalizability of `h`. It works over any field of characteristic zero.

For the adjoint module this is the direct sum `L = [L, e] ⊕ ker (ad f)`. The first summand is the
image of the differential of the orbit map `g ↦ Ad g e` of a group with Lie algebra `L`. The second
is the direction of the affine subspace `e + ker (ad f)`, the Slodowy slice at `e`. So the
decomposition is the linear-algebraic content of the transversality of the slice to the adjoint
orbit of `e`. A dimension count also gives `dim ker (ad e) = dim ker (ad f)`: the direction of the
slice has the dimension of the centralizer of `e`.

## The argument

Write `E`, `F`, `H` for the operators by which `e`, `f`, `h` act. Both `E` and `F` are nilpotent.
Disjointness of `range E` and `ker F` is proved by descending induction on `k ≥ 1`: no nonzero
vector of `range (E ^ k)` is killed by `F`. For large `k` the range is zero. For the step, let
`v = E ^ (n + 1) w` with `F v = 0`. The commutation formula for `F` past `E ^ (n + 1)` shows that
`H v - (n + 2) • v` lies in `range (E ^ (n + 2))`. It is also killed by `F`, so it vanishes by the
induction hypothesis. Then `v` is a vector of `ker F` on which `H` acts by `n + 2`. Morozov's
eigenvalue lemma, `TauCeti.Sl2.exists_eq_natCast_of_apply_eq_smul`, applied to the triple
`(-h, f, e)`, says that `H` acts on nonzero vectors of `ker F` only by integers `≤ 0`. Hence
`v = 0`.

The same statement for `(-h, f, e)` gives that `range F` and `ker E` are disjoint. In finite
dimension the two disjointness statements together with rank-nullity force
`dim ker E = dim ker F`. Hence `range E` and `ker F` have complementary dimensions.

## Main results

* `TauCeti.Sl2.disjoint_range_ker`: for operators with nilpotent `E` and `F` satisfying the `sl₂`
  relations, `range E` and `ker F` are disjoint. No finiteness is assumed.
* `IsSl2Triple.isNilpotent_toEnd_e` and `IsSl2Triple.isNilpotent_toEnd_f`: in a
  finite-dimensional module, `e` and `f` act nilpotently.
* `IsSl2Triple.isCompl_range_toEnd_e_ker_toEnd_f`: **the decomposition** `M = e • M ⊕ ker f`.
* `IsSl2Triple.finrank_ker_toEnd_e_eq_finrank_ker_toEnd_f`: the highest and lowest weight vectors
  span subspaces of the same dimension.
* `IsSl2Triple.isCompl_range_ad_e_ker_ad_f` and
  `IsSl2Triple.finrank_ker_ad_e_eq_finrank_ker_ad_f`: the adjoint forms.

## References

* P. Slodowy, *Simple Singularities and Simple Algebraic Groups*, Lecture Notes in Mathematics
  **815**, Springer, 1980, Chapter 7, for the slice `e + ker (ad f)` and its transversality.
* D. H. Collingwood and W. M. McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*, Van
  Nostrand Reinhold, 1993, Chapter 3, for the `sl₂` theory of nilpotent elements.
* V. V. Morozov, *On a nilpotent element in a semi-simple Lie algebra*, C. R. (Doklady) Acad.
  Sci. URSS (N.S.) **36** (1942), 83–86, for the eigenvalue lemma used in the induction.
-/

public section

namespace TauCeti

namespace Sl2

variable {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]
  {E F H : Module.End K V}

/-- If `v ∈ range (E ^ (n + 1))` is killed by `F`, then `H v - (n + 2) • v` lies in
`range (E ^ (n + 2))` and is killed by `F`. -/
private theorem apply_sub_smul_mem_range_pow_and_apply_eq_zero (hef : E * F - F * E = H)
    (hhe : H * E - E * H = 2 • E) (hhf : H * F - F * H = -(2 • F)) {n : ℕ} {v : V}
    (hv : v ∈ LinearMap.range (E ^ (n + 1))) (hFv : F v = 0) :
    H v - ((n + 2 : ℕ) : K) • v ∈ LinearMap.range (E ^ (n + 2)) ∧
      F (H v - ((n + 2 : ℕ) : K) • v) = 0 := by
  refine ⟨?_, ?_⟩
  · obtain ⟨w, rfl⟩ := hv
    refine ⟨((n + 1 : ℕ) : K)⁻¹ • F w, ?_⟩
    -- `F v = E ^ (n + 1) (F w) - (n + 1) • E ^ n ((H + n) w)`, and `F v = 0`.
    have h₁ := congr(E $(congr($(f_mul_e_pow_succ hef hhe n) w)))
    -- `H v = E ^ (n + 1) ((H + 2 (n + 1)) w)`.
    have h₂ : H * E ^ (n + 1) = E ^ (n + 1) * (H + ((2 * (n + 1) : ℕ) : Module.End K V)) := by
      rw [h_mul_e_pow hhe, Nat.cast_mul, Nat.cast_ofNat]
    have h₂ := congr($h₂ w)
    simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply, map_sub,
      LinearMap.add_apply, Module.End.natCast_apply, map_add, hFv, map_zero,
      ← Nat.cast_smul_eq_nsmul K, map_smul] at h₁ h₂
    simp only [pow_succ', Module.End.mul_apply, map_smul] at h₁ h₂ ⊢
    rw [eq_of_sub_eq_zero h₁.symm, smul_smul,
      inv_mul_cancel₀ (Nat.cast_ne_zero.mpr n.succ_ne_zero), one_smul]
    push_cast at h₂ ⊢
    linear_combination (norm := module) -h₂
  · -- `F H = H F + 2 F`, so `F` kills `H v` along with `v`.
    have := congr($hhf v)
    simp only [LinearMap.sub_apply, Module.End.mul_apply, hFv, map_zero, LinearMap.neg_apply,
      LinearMap.smul_apply, smul_zero, neg_zero, zero_sub, neg_eq_zero] at this
    simp [this, hFv]

/-- Let `E` and `F` be nilpotent operators satisfying the `sl₂` relations with `H`. Then no nonzero
vector in the range of `E` is killed by `F`. No finiteness is needed. -/
theorem disjoint_range_ker (hE : IsNilpotent E) (hF : IsNilpotent F) (hef : E * F - F * E = H)
    (hhe : H * E - E * H = 2 • E) (hhf : H * F - F * H = -(2 • F)) :
    Disjoint (LinearMap.range E) (LinearMap.ker F) := by
  obtain ⟨m, hm⟩ := hE
  -- The triple `(-H, F, E)` satisfies the hypotheses of Morozov's eigenvalue lemma.
  have hFE : F * E - E * F = -H := by rw [← hef, neg_sub]
  have hHF : -H * F - F * -H = 2 • F := by
    rw [neg_mul, mul_neg, ← neg_neg (2 • F), ← hhf]
    abel
  -- Descending induction: `range (E ^ (k + 1))` meets `ker F` trivially.
  suffices ∀ d k, m ≤ k + 1 + d →
      ∀ v ∈ LinearMap.range (E ^ (k + 1)), F v = 0 → v = 0 by
    rw [Submodule.disjoint_def]
    intro v hv hFv
    exact this m 0 (by omega) v (by simpa using hv) hFv
  intro d
  induction d with
  | zero =>
    rintro k hk v ⟨w, rfl⟩ -
    rw [pow_eq_zero_of_le (by omega) hm, LinearMap.zero_apply]
  | succ d ih =>
    intro k hk v hv hFv
    obtain ⟨hmem, hFu⟩ := apply_sub_smul_mem_range_pow_and_apply_eq_zero hef hhe hhf hv hFv
    have hHv : H v = ((k + 2 : ℕ) : K) • v := sub_eq_zero.mp (ih (k + 1) (by omega) _ hmem hFu)
    by_contra hv0
    obtain ⟨n, hn⟩ := exists_eq_natCast_of_apply_eq_smul hF hFE hHF hFv hv0
      (a := -((k + 2 : ℕ) : K)) (by rw [LinearMap.neg_apply, hHv, neg_smul])
    exact absurd hn (by exact_mod_cast (by omega : -((k + 2 : ℕ) : ℤ) ≠ n))

end Sl2

end TauCeti

namespace IsSl2Triple

open LieModule LieAlgebra Module

variable {K L M : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M] [FiniteDimensional K M]
  {h e f : L}

/-- The raising element of an `sl₂` triple acts nilpotently on a finite-dimensional module over a
field of characteristic zero. -/
theorem isNilpotent_toEnd_e (t : IsSl2Triple h e f) : IsNilpotent (toEnd K L M e) :=
  TauCeti.isNilpotent_apply_of_lie_eq_smul (two_ne_zero (α := K)) (t.lie_h_e_smul K)

/-- The lowering element of an `sl₂` triple acts nilpotently on a finite-dimensional module over a
field of characteristic zero. -/
theorem isNilpotent_toEnd_f (t : IsSl2Triple h e f) : IsNilpotent (toEnd K L M f) :=
  t.symm.isNilpotent_toEnd_e

attribute [local instance 100] LieRing.ofAssociativeRing in
/-- The range of the raising operator meets the kernel of the lowering operator trivially. -/
private theorem disjoint_range_toEnd_e_ker_toEnd_f (t : IsSl2Triple h e f) :
    Disjoint (LinearMap.range (toEnd K L M e)) (LinearMap.ker (toEnd K L M f)) := by
  refine TauCeti.Sl2.disjoint_range_ker (H := toEnd K L M h) t.isNilpotent_toEnd_e
    t.isNilpotent_toEnd_f ?_ ?_ ?_
  · rw [← Ring.lie_def, ← LieHom.map_lie, t.lie_e_f]
  · rw [← Ring.lie_def, ← LieHom.map_lie, t.lie_h_e_nsmul, map_nsmul]
  · rw [← Ring.lie_def, ← LieHom.map_lie, t.lie_h_f_nsmul, map_neg, map_nsmul]

/-- The kernels of the raising and lowering operators of an `sl₂` triple on a finite-dimensional
module have the same dimension. These are the spaces of highest and of lowest weight vectors. -/
theorem finrank_ker_toEnd_e_eq_finrank_ker_toEnd_f (t : IsSl2Triple h e f) :
    finrank K (LinearMap.ker (toEnd K L M e)) = finrank K (LinearMap.ker (toEnd K L M f)) := by
  have h₁ := Submodule.finrank_add_finrank_le_of_disjoint
    (t.disjoint_range_toEnd_e_ker_toEnd_f (K := K) (M := M))
  have h₂ := Submodule.finrank_add_finrank_le_of_disjoint
    (t.symm.disjoint_range_toEnd_e_ker_toEnd_f (K := K) (M := M))
  have h₃ := LinearMap.finrank_range_add_finrank_ker (toEnd K L M e)
  have h₄ := LinearMap.finrank_range_add_finrank_ker (toEnd K L M f)
  omega

/-- **The `sl₂` decomposition `M = e • M ⊕ ker f`.** For an `sl₂` triple `(h, e, f)` acting on a
finite-dimensional module over a field of characteristic zero, the range of the raising operator
and the kernel of the lowering operator are complementary. -/
theorem isCompl_range_toEnd_e_ker_toEnd_f (t : IsSl2Triple h e f) :
    IsCompl (LinearMap.range (toEnd K L M e)) (LinearMap.ker (toEnd K L M f)) := by
  refine (Submodule.isCompl_iff_disjoint _ _ ?_).mpr t.disjoint_range_toEnd_e_ker_toEnd_f
  have := LinearMap.finrank_range_add_finrank_ker (toEnd K L M e)
  rw [← t.finrank_ker_toEnd_e_eq_finrank_ker_toEnd_f]
  omega

variable [FiniteDimensional K L]

/-- **The transverse decomposition `L = [L, e] ⊕ ker (ad f)`.** For an `sl₂` triple `(h, e, f)` in a
finite-dimensional Lie algebra over a field of characteristic zero, the range of `ad e` and the
kernel of `ad f` are complementary. -/
theorem isCompl_range_ad_e_ker_ad_f (t : IsSl2Triple h e f) :
    IsCompl (LinearMap.range (ad K L e)) (LinearMap.ker (ad K L f)) :=
  -- `ad K L` is by definition the action `toEnd K L L` of `L` on itself.
  t.isCompl_range_toEnd_e_ker_toEnd_f (M := L)

/-- The centralizers of the raising and lowering elements of an `sl₂` triple in a
finite-dimensional Lie algebra over a field of characteristic zero have the same dimension. -/
theorem finrank_ker_ad_e_eq_finrank_ker_ad_f (t : IsSl2Triple h e f) :
    finrank K (LinearMap.ker (ad K L e)) = finrank K (LinearMap.ker (ad K L f)) :=
  -- `ad K L` is by definition the action `toEnd K L L` of `L` on itself.
  t.finrank_ker_toEnd_e_eq_finrank_ker_toEnd_f (M := L)

end IsSl2Triple
