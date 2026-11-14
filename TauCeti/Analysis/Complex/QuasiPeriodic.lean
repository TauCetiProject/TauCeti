/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.Complex.Liouville
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Algebra.Module.ZLattice.Basic
import TauCeti.Analysis.Complex.Circle

/-!
# Holomorphic sections of flat unitary line bundles on complex tori

Let `V` be a finite-dimensional complex normed space and `L ⊆ V` a full lattice, so that `V ⧸ L`
is a compact complex torus. A unitary character `ψ : L → S¹` (an `AddChar L Circle`) defines the
flat unitary line bundle `(V × ℂ) ⧸ L` on `V ⧸ L`, for the action `ω • (z, v) = (z + ω, ψ ω v)`;
its holonomy around the loop of `ω ∈ L` is `ψ ω`. Its holomorphic sections with values in a
complex normed space `F` are the entire maps `f : V → F` that are quasi-periodic with multiplier
`ψ`:

`f (z + ω) = ψ ω • f z` for every `ω ∈ L`.

Since `|ψ ω| = 1`, the norm of such a map is `L`-periodic, hence bounded on the compact torus, so
the map is constant by Liouville's theorem
(`Differentiable.apply_eq_apply_of_norm_add_eq`). A nonzero constant is quasi-periodic only for the
trivial multiplier, so a nontrivial flat unitary line bundle has no nonzero holomorphic section
(`Differentiable.eq_zero_of_add_eq_smul`, and the characterization
`TauCeti.exists_differentiable_ne_zero_add_eq_smul_iff`).

The `j`-th power `N ^ j` of the flat line `N` of `ψ` is the flat line of `ψ ^ j`. A finite
covering of `V ⧸ L` by a torus is `V ⧸ L' → V ⧸ L` for a subgroup `L' ≤ L` of finite index, and
the pull-back of `N` to it is the flat line of the restriction of `ψ` to `L'`. If some holonomy
`ψ ω₀` has infinite order, then `ψ (n • ω₀) ^ j = ψ ω₀ ^ (n j)` is never `1` for `n, j > 0`.
Since some positive multiple of `ω₀` lies in `L'`, every positive power of `N`, pulled back to
every finite covering torus, is a nontrivial flat line, and so has no nonzero holomorphic section
(`Differentiable.eq_zero_of_add_eq_pow_smul`). The holonomy `exp (2π i x)` has infinite order
exactly when `x` is irrational (`Circle.isOfFinOrder_exp_two_pi_mul_iff`), which gives such
characters on every nonzero lattice (`Differentiable.eq_zero_of_add_eq_fourierChar_pow_smul`).

For a square-zero torus `C` in a symplectic four-manifold, with a flat normal line `N` of
irrational holonomy, the last statement is the vanishing of holomorphic sections of `N ^ j` on
every finite cover of `C`: the Cauchy–Riemann operators of these lines have zero kernel. This
is the input which forces the coefficients `b_j ∈ H⁰(C, N ^ j)`, `1 ≤ j ≤ m`, of a compact
holomorphic curve in the total space of `N` covering `C` with degree `m` to vanish, so that the
curve lies on the zero section; that application is not formalized here.

For a lattice in `ℂ` with a basis `ω₁, ω₂`, `TauCeti.Analysis.Complex.Wirtinger.FlatTorus` proves
the quantitative counterpart: an `L²` coercivity estimate for `∂bar` on `C²` sections over the
fundamental parallelogram, with a positive constant on every power and on every finite cover
given by an integer change of basis of nonzero determinant, namely
`TauCeti.exists_pos_mul_setIntegral_norm_sq_le_setIntegral_norm_conjWirtingerDeriv_sq_of_irrational`
(using `TauCeti.notMem_range_intCast_or_notMem_range_intCast_of_irrational`). That estimate is what
a bounded inverse of `∂bar` needs. The statements here are the qualitative form used for the
coefficients `b_j` above, which are entire quasi-periodic maps: they apply to entire maps
directly, without a fundamental-domain integral, on a torus of any dimension, for any subgroup of
finite index and any holonomy of infinite order, and they come with the converse for the trivial
line.

## Main results

* `Differentiable.apply_eq_apply_of_norm_add_eq`: an entire map whose norm is invariant under
  translation by a full lattice is constant.
* `Differentiable.eq_zero_of_add_eq_smul`: a quasi-periodic entire map with nontrivial unitary
  multiplier vanishes.
* `TauCeti.exists_differentiable_ne_zero_add_eq_smul_iff`: a flat unitary line bundle on a complex
  torus has a nonzero holomorphic section exactly when it is trivial.
* `Differentiable.eq_zero_of_add_eq_pow_smul`: if some holonomy has infinite order, the
  holomorphic sections of every positive power of the flat line, on every finite covering torus,
  vanish.
* `Differentiable.eq_zero_of_add_eq_fourierChar_pow_smul`: the same for the flat line of holonomy
  `exp (2π i c ω)`, where `c` takes an irrational value on the lattice.

## References

* David Mumford, *Abelian Varieties*, Tata Institute of Fundamental Research Studies in
  Mathematics 5, Oxford University Press, 1970, Chapter I, §2 (line bundles on complex tori as
  factors of automorphy; the Appell–Humbert theorem).
* Christina Birkenhake and Herbert Lange, *Complex Abelian Varieties*, second edition,
  Grundlehren der mathematischen Wissenschaften 302, Springer, 2004, Chapter 2 (line bundles on
  complex tori).
* C. H. Taubes, *Counting pseudo-holomorphic submanifolds in dimension 4*, J. Differential Geom.
  44 (1996), 818–893 (square-zero tori and their finite covers).
-/

public section

open Bornology Set

variable {V F : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup F] [NormedSpace ℂ F] {f : V → F}

namespace Differentiable

/-- **Liouville's theorem on a complex torus.** An entire map whose norm is invariant under
translation by a full lattice `L` is constant: its norm is the norm of a continuous function on the
compact torus `V ⧸ L`, so it is bounded. -/
theorem apply_eq_apply_of_norm_add_eq (hf : Differentiable ℂ f) (L : Submodule ℤ V)
    [DiscreteTopology L] [IsZLattice ℝ L] (h : ∀ z, ∀ ω ∈ L, ‖f (z + ω)‖ = ‖f z‖) (z w : V) :
    f z = f w := by
  refine hf.apply_eq_apply_of_bounded ?_ z w
  obtain ⟨C, hC⟩ := (IsZLattice.isCompact_range_of_periodic L (fun z ↦ ‖f z‖)
    hf.continuous.norm fun z ω hω ↦ h z ω hω).isBounded.exists_norm_le
  refine isBounded_iff_forall_norm_le.2 ⟨C, ?_⟩
  rintro - ⟨z, rfl⟩
  simpa using hC _ (mem_range_self z)

/-- **A nontrivial flat unitary line bundle on a complex torus has no nonzero holomorphic
section.** An entire map that is quasi-periodic for a full lattice `L`, with a nontrivial unitary
multiplier `ψ`, vanishes. -/
theorem eq_zero_of_add_eq_smul (hf : Differentiable ℂ f) {L : Submodule ℤ V}
    [DiscreteTopology L] [IsZLattice ℝ L] {ψ : AddChar L Circle} (hψ : ψ ≠ 1)
    (h : ∀ z (ω : L), f (z + ω) = (ψ ω : ℂ) • f z) : f = 0 := by
  obtain ⟨ω, hω⟩ := DFunLike.ne_iff.1 hψ
  have hconst := hf.apply_eq_apply_of_norm_add_eq L fun z ω' hω' ↦ by
    simp [h z ⟨ω', hω'⟩, norm_smul]
  ext z
  -- `f` is constant, and the constant is fixed by the multiplier `ψ ω ≠ 1`.
  have hz : ((ψ ω : ℂ) - 1) • f z = 0 := by
    rw [sub_smul, one_smul, ← h z ω, hconst (z + ω) z, sub_self]
  exact (smul_eq_zero.1 hz).resolve_left (sub_ne_zero.2 (by simpa [Circle.coe_eq_one] using hω))

/-- **Finite covers and powers of a flat line of infinite-order holonomy.** Let `ψ` be a unitary
character of a full lattice `L` taking a value of infinite order. Then for every subgroup `L' ≤ L`
of finite index and every `j ≠ 0`, an entire map that is quasi-periodic for `L'` with multiplier
`ψ ^ j` vanishes: the flat line `N ^ j` pulled back to the finite covering torus `V ⧸ L'` has no
nonzero holomorphic section. -/
theorem eq_zero_of_add_eq_pow_smul (hf : Differentiable ℂ f) {L : Submodule ℤ V}
    [DiscreteTopology L] [IsZLattice ℝ L] {ψ : AddChar L Circle} {ω₀ : L}
    (hω₀ : ¬IsOfFinOrder (ψ ω₀)) {L' : Submodule ℤ V} (hL' : L' ≤ L)
    (hidx : L'.toAddSubgroup.relIndex L.toAddSubgroup ≠ 0) {j : ℕ} (hj : j ≠ 0)
    (h : ∀ z, ∀ (ω) (hω : ω ∈ L'), f (z + ω) = (ψ ⟨ω, hL' hω⟩ : ℂ) ^ j • f z) : f = 0 := by
  have : DiscreteTopology L' := .of_subset ‹DiscreteTopology L› hL'
  have : IsZLattice ℝ L' := IsZLattice.of_relIndex_ne_zero hidx
  -- The holonomy of the pulled-back power `N ^ j` around `n • ω₀ ∈ L'` is `ψ ω₀ ^ (n * j)`.
  obtain ⟨n, hn, -, hmem⟩ := AddSubgroup.exists_nsmul_mem_of_relIndex_ne_zero hidx ω₀.2
  refine hf.eq_zero_of_add_eq_smul
    (ψ := (ψ ^ j).compAddMonoidHom (Submodule.inclusion hL').toAddMonoidHom) ?_
    fun z ω ↦ by simpa [Submodule.inclusion_apply] using h z ω ω.2
  intro h1
  refine hω₀ (isOfFinOrder_iff_pow_eq_one.2 ⟨n * j, Nat.mul_pos hn (Nat.pos_of_ne_zero hj), ?_⟩)
  have h2 := DFunLike.congr_fun h1 ⟨n • (ω₀ : V), hmem.1⟩
  have h3 : Submodule.inclusion hL' ⟨n • (ω₀ : V), hmem.1⟩ = n • ω₀ := Subtype.ext (by simp)
  simp only [AddChar.compAddMonoidHom_apply, LinearMap.toAddMonoidHom_coe, h3, pow_apply,
    AddChar.map_nsmul_eq_pow, one_apply] at h2
  rwa [pow_mul]

/-- **Flat lines of irrational holonomy.** Let `c : L →+ ℝ` take an irrational value on some
lattice vector, and let `N` be the flat line on `V ⧸ L` with holonomy `exp (2π i c ω)` around `ω`.
Then for every subgroup `L' ≤ L` of finite index and every `j ≠ 0`, the holomorphic sections of
`N ^ j` pulled back to `V ⧸ L'` vanish. -/
theorem eq_zero_of_add_eq_fourierChar_pow_smul (hf : Differentiable ℂ f) {L : Submodule ℤ V}
    [DiscreteTopology L] [IsZLattice ℝ L] {c : L →+ ℝ} {ω₀ : L} (hω₀ : Irrational (c ω₀))
    {L' : Submodule ℤ V} (hL' : L' ≤ L) (hidx : L'.toAddSubgroup.relIndex L.toAddSubgroup ≠ 0)
    {j : ℕ} (hj : j ≠ 0)
    (h : ∀ z, ∀ (ω) (hω : ω ∈ L'), f (z + ω) = (Real.fourierChar (c ⟨ω, hL' hω⟩) : ℂ) ^ j • f z) :
    f = 0 :=
  hf.eq_zero_of_add_eq_pow_smul (ψ := Real.fourierChar.compAddMonoidHom c) (ω₀ := ω₀)
    (by simpa [Real.fourierChar_apply', Circle.isOfFinOrder_exp_two_pi_mul_iff] using hω₀)
    hL' hidx hj fun z ω hω ↦ by simpa using h z ω hω

end Differentiable

namespace TauCeti

/-- **Holomorphic sections of flat unitary line bundles on a complex torus.** The flat unitary line
bundle of a character `ψ` of a full lattice `L` has a nonzero holomorphic section, with values in
a nontrivial complex normed space `F`, exactly when `ψ` is trivial; the sections of the trivial
bundle are the constants. -/
theorem exists_differentiable_ne_zero_add_eq_smul_iff (F : Type*) [NormedAddCommGroup F]
    [NormedSpace ℂ F] [Nontrivial F] {L : Submodule ℤ V} [DiscreteTopology L] [IsZLattice ℝ L]
    (ψ : AddChar L Circle) :
    (∃ f : V → F, Differentiable ℂ f ∧ f ≠ 0 ∧ ∀ z (ω : L), f (z + ω) = (ψ ω : ℂ) • f z) ↔
      ψ = 1 := by
  refine ⟨fun ⟨f, hf, hf0, h⟩ ↦ by_contra fun hψ ↦ hf0 (hf.eq_zero_of_add_eq_smul hψ h), ?_⟩
  rintro rfl
  obtain ⟨v, hv⟩ := exists_ne (0 : F)
  exact ⟨fun _ ↦ v, differentiable_const v, fun h0 ↦ hv (congr_fun h0 0), by simp⟩

end TauCeti
