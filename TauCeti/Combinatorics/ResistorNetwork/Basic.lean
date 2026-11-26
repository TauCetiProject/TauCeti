/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Basic.Real.Basic

/-!
# Finite resistor networks and their Laplacians

A resistor network on a vertex type `V` is a family of edges, indexed by a type `E`, each joining
two vertices and carrying a positive resistance. Parallel edges and loops are allowed. Every edge
is given an orientation `src e → tgt e`; it only fixes the sign convention for the current through
the edge, and nothing in the electrical theory depends on it.

The weighted Laplacian of a finite network sends a potential `f : V → ℝ` to the net current
`(L f) v = ∑ (f v - f w) / r` leaving each vertex `v`, the sum running over the edges at `v`, with
`w` the other end of the edge and `r` its resistance. Its quadratic form is the Dirichlet energy
`∑ₑ (f (src e) - f (tgt e))² / rₑ`. This file proves the basic linear algebra of the Laplacian that
underlies the theory of effective resistance:

* `TauCeti.ResistorNetwork.sum_mul_laplacian_apply`: Green's identity, which expresses the
  Laplacian pairing `∑ᵥ g v * (L f) v` as a sum over edges; in particular the Laplacian is
  symmetric (`TauCeti.ResistorNetwork.sum_mul_laplacian_apply_comm`) and its quadratic form is the
  energy.
* `TauCeti.ResistorNetwork.laplacian_eq_zero_iff`: the harmonic potentials are those that are
  constant along every edge, hence (`TauCeti.ResistorNetwork.ker_laplacian`) the constants when
  the network is connected.
* `TauCeti.ResistorNetwork.mem_range_laplacian_iff`: on a connected network every function of
  total sum zero is the Laplacian of a potential, so that the Kirchhoff equations for any
  external current of total zero are solvable.

## References

* M. Baker and X. Faber, *Metrized graphs, Laplacian operators, and electrical networks*,
  Quantum graphs and their applications, Contemp. Math. 415 (2006), §§1–2.
* B. Bollobás, *Modern Graph Theory*, Graduate Texts in Mathematics 184, Springer, 1998,
  Chapter II.
-/

public section

open Finset Module

namespace TauCeti

/-- A resistor network: each edge `e : E` is a resistor of resistance `resistance e > 0` joining
the vertices `src e` and `tgt e`. Parallel edges and loops are allowed. The orientation of an edge
only fixes the sign of the current through it. -/
structure ResistorNetwork (V E : Type*) where
  /-- The vertex at which an edge starts. -/
  src : E → V
  /-- The vertex at which an edge ends. -/
  tgt : E → V
  /-- The resistance of an edge. -/
  resistance : E → ℝ
  /-- Every resistance is positive. -/
  resistance_pos : ∀ e, 0 < resistance e

namespace ResistorNetwork

variable {V E : Type*} (N : ResistorNetwork V E)

/-- No resistance vanishes. -/
theorem resistance_ne_zero (e : E) : N.resistance e ≠ 0 :=
  (N.resistance_pos e).ne'

/-- The simple graph in which two distinct vertices are adjacent when some edge of the network
joins them. It records the connectivity of the network. -/
def toSimpleGraph : SimpleGraph V :=
  SimpleGraph.fromRel fun x y => ∃ e, N.src e = x ∧ N.tgt e = y

/-- Two vertices are adjacent when they are distinct and some edge joins them, in either
direction. -/
@[simp] theorem toSimpleGraph_adj {x y : V} :
    N.toSimpleGraph.Adj x y ↔
      x ≠ y ∧ ((∃ e, N.src e = x ∧ N.tgt e = y) ∨ ∃ e, N.src e = y ∧ N.tgt e = x) :=
  SimpleGraph.fromRel_adj _ x y

/-- A function constant along every edge of a preconnected network is constant. -/
theorem apply_eq_apply_of_preconnected {α : Type*} (hN : N.toSimpleGraph.Preconnected)
    {f : V → α} (hf : ∀ e, f (N.src e) = f (N.tgt e)) (a b : V) : f a = f b := by
  have hadj : ∀ x y, N.toSimpleGraph.Adj x y → f x = f y := by
    rintro x y hxy
    obtain ⟨-, ⟨e, rfl, rfl⟩ | ⟨e, rfl, rfl⟩⟩ := N.toSimpleGraph_adj.1 hxy
    · exact hf e
    · exact (hf e).symm
  induction (SimpleGraph.reachable_iff_reflTransGen a b).1 (hN a b) with
  | refl => rfl
  | tail _ hxy ih => exact ih.trans (hadj _ _ hxy)

/-- The energy dissipated in an edge by a voltage drop `x` across it is nonnegative. -/
theorem sq_div_resistance_nonneg (x : ℝ) (e : E) : 0 ≤ x ^ 2 / N.resistance e :=
  div_nonneg (sq_nonneg x) (N.resistance_pos e).le

variable [Fintype E] [DecidableEq V]

/-- The weighted Laplacian of a finite network: `(L f) v` is the current leaving `v` for the
potential `f`, the sum over the edges at `v` of `(f v - f w) / r`, where `w` is the other end of
the edge and `r` its resistance. -/
noncomputable def laplacian : (V → ℝ) →ₗ[ℝ] V → ℝ :=
  ∑ e, (N.resistance e)⁻¹ •
    ((LinearMap.proj (N.src e) : (V → ℝ) →ₗ[ℝ] ℝ) - LinearMap.proj (N.tgt e)).smulRight
      (Pi.single (N.src e) 1 - Pi.single (N.tgt e) 1 : V → ℝ)

/-- The Laplacian is the sum over the edges of the current through the edge, sent out of its
source and into its target. -/
theorem laplacian_apply (f : V → ℝ) :
    N.laplacian f = ∑ e, ((f (N.src e) - f (N.tgt e)) / N.resistance e) •
      (Pi.single (N.src e) 1 - Pi.single (N.tgt e) 1 : V → ℝ) := by
  simp [laplacian, LinearMap.sum_apply, smul_smul, div_eq_inv_mul]

/-- The Laplacian at a vertex is the total current through the edges leaving it, minus the total
current through the edges entering it. A loop contributes nothing. -/
theorem laplacian_apply_apply (f : V → ℝ) (v : V) :
    N.laplacian f v =
      ∑ e with N.src e = v, (f (N.src e) - f (N.tgt e)) / N.resistance e -
        ∑ e with N.tgt e = v, (f (N.src e) - f (N.tgt e)) / N.resistance e := by
  simp [laplacian_apply, Finset.sum_apply, Pi.single_apply, mul_sub, Finset.sum_sub_distrib,
    Finset.sum_ite, eq_comm]

variable [Fintype V]

/-- **Green's identity**: the Laplacian pairing of two potentials is the sum over the edges of
the product of their differences, divided by the resistance. -/
theorem sum_mul_laplacian_apply (f g : V → ℝ) :
    ∑ v, g v * N.laplacian f v =
      ∑ e, (g (N.src e) - g (N.tgt e)) * (f (N.src e) - f (N.tgt e)) / N.resistance e := by
  simp only [laplacian_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => ?_
  simp only [Pi.sub_apply, Pi.single_apply, mul_sub, mul_ite, mul_one, mul_zero,
    Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

/-- The Laplacian is symmetric. -/
theorem sum_mul_laplacian_apply_comm (f g : V → ℝ) :
    ∑ v, g v * N.laplacian f v = ∑ v, f v * N.laplacian g v := by
  simp only [sum_mul_laplacian_apply, mul_comm (g _ - g _)]

/-- The quadratic form of the Laplacian is the Dirichlet energy. -/
theorem sum_mul_laplacian_apply_self (f : V → ℝ) :
    ∑ v, f v * N.laplacian f v = ∑ e, (f (N.src e) - f (N.tgt e)) ^ 2 / N.resistance e := by
  simp only [sum_mul_laplacian_apply, sq]

/-- The Dirichlet energy is nonnegative. -/
theorem sum_mul_laplacian_apply_self_nonneg (f : V → ℝ) : 0 ≤ ∑ v, f v * N.laplacian f v := by
  rw [sum_mul_laplacian_apply_self]
  exact Finset.sum_nonneg fun e _ => N.sq_div_resistance_nonneg _ e

/-- Every Laplacian has total sum zero: the currents leaving the vertices cancel. -/
@[simp] theorem sum_laplacian_apply (f : V → ℝ) : ∑ v, N.laplacian f v = 0 := by
  simpa using N.sum_mul_laplacian_apply f 1

omit [Fintype V] in
/-- A potential is harmonic exactly when it is constant along every edge. -/
theorem laplacian_eq_zero_iff [Finite V] {f : V → ℝ} :
    N.laplacian f = 0 ↔ ∀ e, f (N.src e) = f (N.tgt e) := by
  have := Fintype.ofFinite V
  refine ⟨fun hf e => ?_, fun hf => by simp [laplacian_apply, hf]⟩
  have h := N.sum_mul_laplacian_apply_self f
  rw [hf] at h
  simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero] at h
  have := (Finset.sum_eq_zero_iff_of_nonneg fun e _ =>
    N.sq_div_resistance_nonneg _ e).1 h.symm e (Finset.mem_univ e)
  rw [div_eq_zero_iff, or_iff_left (N.resistance_ne_zero e), sq_eq_zero_iff, sub_eq_zero] at this
  exact this

omit [Fintype V] in
/-- On a preconnected network the harmonic potentials are the constants. -/
theorem ker_laplacian [Finite V] (hN : N.toSimpleGraph.Preconnected) :
    LinearMap.ker N.laplacian = ℝ ∙ (1 : V → ℝ) := by
  ext f
  rw [LinearMap.mem_ker, laplacian_eq_zero_iff, Submodule.mem_span_singleton]
  refine ⟨fun hf => ?_, ?_⟩
  · cases isEmpty_or_nonempty V with
    | inl _ => exact ⟨0, Subsingleton.elim _ _⟩
    | inr h =>
      obtain ⟨a⟩ := h
      exact ⟨f a, funext fun b => by simp [N.apply_eq_apply_of_preconnected hN hf a b]⟩
  · rintro ⟨c, rfl⟩ e
    simp

omit [Fintype V] in
/-- The harmonic potentials of a connected network form a line. -/
theorem finrank_ker_laplacian [Finite V] (hN : N.toSimpleGraph.Connected) :
    finrank ℝ (LinearMap.ker N.laplacian) = 1 := by
  have := hN.nonempty
  rw [N.ker_laplacian hN.preconnected]
  exact finrank_span_singleton one_ne_zero

/-- The Laplacian of a preconnected network has rank one less than the number of vertices. -/
theorem finrank_range_laplacian (hN : N.toSimpleGraph.Preconnected) :
    finrank ℝ (LinearMap.range N.laplacian) = Fintype.card V - 1 := by
  have h := N.laplacian.finrank_range_add_finrank_ker
  rw [Module.finrank_fintype_fun_eq_card] at h
  cases isEmpty_or_nonempty V with
  | inl _ => simp only [Fintype.card_eq_zero, Nat.zero_sub] at h ⊢; omega
  | inr _ =>
    rw [N.finrank_ker_laplacian ⟨hN⟩] at h
    omega

/-- On a preconnected network, a function is the Laplacian of a potential exactly when its total
sum vanishes: the Kirchhoff equations are solvable for every external current of total zero. -/
theorem mem_range_laplacian_iff (hN : N.toSimpleGraph.Preconnected) {g : V → ℝ} :
    g ∈ LinearMap.range N.laplacian ↔ ∑ v, g v = 0 := by
  cases isEmpty_or_nonempty V with
  | inl _ => simp [Subsingleton.elim g 0]
  | inr hV =>
    -- The range lies in the kernel of the total-sum functional, and both have codimension one.
    let σ : (V → ℝ) →ₗ[ℝ] ℝ := ∑ v, LinearMap.proj v
    have hσ (h : V → ℝ) : σ h = ∑ v, h v := by simp [σ, LinearMap.sum_apply]
    have hle : LinearMap.range N.laplacian ≤ LinearMap.ker σ := by
      rintro _ ⟨f, rfl⟩
      simp [hσ]
    have hσ_surj : LinearMap.range σ = ⊤ := by
      obtain ⟨a⟩ := hV
      refine LinearMap.range_eq_top.2 fun t => ⟨Pi.single a t, ?_⟩
      simp [hσ]
    have hker := σ.finrank_range_add_finrank_ker
    rw [hσ_surj, finrank_top, Module.finrank_self, Module.finrank_fintype_fun_eq_card] at hker
    have heq : LinearMap.range N.laplacian = LinearMap.ker σ :=
      Submodule.eq_of_le_of_finrank_eq hle (by
        rw [N.finrank_range_laplacian hN]
        omega)
    rw [heq, LinearMap.mem_ker, hσ]

end ResistorNetwork

end TauCeti
