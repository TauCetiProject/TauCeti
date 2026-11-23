/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.TensorProduct.Maps
public import TauCeti.RingTheory.TensorProduct.DirectLimit
public import TauCeti.RingTheory.IntegralClosure.FilteredColimits
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
# Integrality of tensor products of algebra morphisms

If `f : S →ₐ[R] S'` and `g : T →ₐ[R] T'` are integral `R`-algebra homomorphisms, then their tensor
product `Algebra.TensorProduct.map f g : S ⊗[R] T →ₐ[R] S' ⊗[R] T'` is also integral
(`RingHom.IsIntegral.tensorProductMap`). This is the integrality counterpart of
`RingHom.Finite.tensorProductMap`.

## Main results

* `RingHom.IsIntegral.tensorProductMap`: tensor product of two integral `R`-algebra homomorphisms
  is integral.
-/

public section

open scoped TensorProduct

/-- The tensor product `Algebra.TensorProduct.map f g : S ⊗[R] T →ₐ[R] S' ⊗[R] T'` of two integral
`R`-algebra homomorphisms `f : S →ₐ[R] S'` and `g : T →ₐ[R] T'` is integral. -/
theorem RingHom.IsIntegral.tensorProductMap
    {R S S' T T' : Type*} [CommRing R] [CommRing S] [CommRing T] [CommRing S'] [CommRing T']
    [Algebra R S] [Algebra R T] [Algebra R S'] [Algebra R T']
    {f : S →ₐ[R] S'} (hf : f.toRingHom.IsIntegral) {g : T →ₐ[R] T'} (hg : g.toRingHom.IsIntegral) :
    (Algebra.TensorProduct.map f g).toRingHom.IsIntegral := by
  intro z
  refine z.inductionOn (fun s' t' ↦ ?_) (fun _ _ hu hv ↦ RingHom.IsIntegralElem.add _ hu hv)
  have hs' : (Algebra.TensorProduct.map f g).toRingHom.IsIntegralElem (s' ⊗ₜ[R] (1 : T')) := by
    have h := (hf s').map
      (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := S') (B := T')).toRingHom
    rw [AlgHom.toRingHom_eq_coe, AlgHom.toRingHom_eq_coe, ← AlgHom.comp_toRingHom,
      ← Algebra.TensorProduct.map_comp_includeLeft f g, AlgHom.comp_toRingHom] at h
    simpa using h.of_comp
  have ht' : (Algebra.TensorProduct.map f g).toRingHom.IsIntegralElem ((1 : S') ⊗ₜ[R] t') := by
    have h := (hg t').map
      (Algebra.TensorProduct.includeRight (R := R) (A := S') (B := T')).toRingHom
    rw [AlgHom.toRingHom_eq_coe, AlgHom.toRingHom_eq_coe, ← AlgHom.comp_toRingHom,
      ← Algebra.TensorProduct.map_comp_includeRight f g, AlgHom.comp_toRingHom] at h
    simpa using h.of_comp
  simpa [Algebra.TensorProduct.tmul_mul_tmul] using RingHom.IsIntegralElem.mul _ hs' ht'

namespace AlgHom

/-- Integrality of a relative pure tensor is preserved by a further scalar extension. -/
theorem isIntegralElem_tensorProductMap_one_tmul
    {S T T' B C : Type*} [CommRing S] [CommRing T] [CommRing T']
    [CommRing B] [Ring C] [Algebra S T] [Algebra S T'] [Algebra S B] [Algebra S C]
    (a : T →ₐ[S] T') (φ : B →ₐ[S] C) (x : C)
    (hx : (Algebra.TensorProduct.map (AlgHom.id S T) φ).IsIntegralElem
      ((1 : T) ⊗ₜ[S] x)) :
    (Algebra.TensorProduct.map (AlgHom.id S T') φ).IsIntegralElem
      ((1 : T') ⊗ₜ[S] x) := by
  let b := Algebra.TensorProduct.map a (AlgHom.id S B)
  let c := Algebra.TensorProduct.map a (AlgHom.id S C)
  have h := hx.map c.toRingHom
  have eq : c.toRingHom.comp (Algebra.TensorProduct.map (AlgHom.id S T) φ).toRingHom =
      (Algebra.TensorProduct.map (AlgHom.id S T') φ).toRingHom.comp b.toRingHom := by
    ext t <;> simp [b, c]
  rw [eq] at h
  have ht : c.toRingHom ((1 : T) ⊗ₜ[S] x) = (1 : T') ⊗ₜ[S] x := by simp [c]
  rw [ht] at h
  exact h.of_comp


end AlgHom

namespace AlgEquiv

/-- A relative pure tensor integral over a directed colimit is integral at some stage. -/
theorem exists_integral_tensor_element
    {S J R : Type*} [CommRing S] [Preorder J] [Nonempty J] [IsDirectedOrder J]
    {T : J → Type*} [∀ j, CommRing (T j)] [∀ j, Algebra S (T j)]
    {trans : ∀ i j, i ≤ j → T i →ₐ[S] T j} [DirectedSystem T (trans · · ·)]
    [CommRing R] [Algebra S R] (e : DirectLimit T trans ≃ₐ[S] R)
    {B₀ C₀ : Type*} [CommRing B₀] [Ring C₀] [Algebra S B₀] [Algebra S C₀]
    (φ₀ : B₀ →ₐ[S] C₀) (x : C₀)
    (hi : (Algebra.TensorProduct.map (AlgHom.id S R) φ₀).IsIntegralElem
      ((1 : R) ⊗ₜ[S] x)) :
    ∃ j, (Algebra.TensorProduct.map (AlgHom.id S (T j)) φ₀).IsIntegralElem
      ((1 : T j) ⊗ₜ[S] x) := by
  let incl (j : J) : T j →ₐ[S] R := e.toAlgHom.comp (DirectLimit.Algebra.of T trans j)
  let B (j : J) := T j ⊗[S] B₀
  let C (j : J) := T j ⊗[S] C₀
  let bmap {i j : J} (h : i ≤ j) : B i →+* B j :=
    (Algebra.TensorProduct.map (trans i j h) (AlgHom.id S B₀)).toRingHom
  let cmap {i j : J} (h : i ≤ j) : C i →+* C j :=
    (Algebra.TensorProduct.map (trans i j h) (AlgHom.id S C₀)).toRingHom
  let bι (j : J) : B j →+* (R ⊗[S] B₀) :=
    (Algebra.TensorProduct.map (incl j) (AlgHom.id S B₀)).toRingHom
  let cι (j : J) : C j →+* (R ⊗[S] C₀) :=
    (Algebra.TensorProduct.map (incl j) (AlgHom.id S C₀)).toRingHom
  let φ (j : J) : B j →+* C j :=
    (Algebra.TensorProduct.map (AlgHom.id S (T j)) φ₀).toRingHom
  let φcolim : (R ⊗[S] B₀) →+* (R ⊗[S] C₀) :=
    (Algebra.TensorProduct.map (AlgHom.id S R) φ₀).toRingHom
  have bcompat {i j : J} (h : i ≤ j) (b : B i) :
      bι j (bmap h b) = bι i b := by
    induction b using TensorProduct.inductionOn with
    | tmul t b =>
      -- Expose the tensor map on a pure tensor before comparing its first factor.
      change incl j (trans i j h t) ⊗ₜ[S] b = incl i t ⊗ₜ[S] b
      congr 1
      -- Expose incl as the colimit inclusion to use of_f.
      change e (DirectLimit.Algebra.of T trans j (trans i j h t)) =
        e (DirectLimit.Algebra.of T trans i t)
      rw [DirectLimit.Algebra.of_f]
    | add x y hx hy => simp only [map_add, hx, hy]
  have φcompat (j : J) (b : B j) : cι j (φ j b) = φcolim (bι j b) := by
    induction b using TensorProduct.inductionOn with
    | tmul t b => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  have φtrans {i j : J} (h : i ≤ j) (b : B i) :
      cmap h (φ i b) = φ j (bmap h b) := by
    induction b using TensorProduct.inductionOn with
    | tmul t b => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  apply TauCeti.integral_at_stage B C bmap cmap bι cι φ φcolim bcompat φcompat φtrans
    (e.exists_rep_and_eventually_zero_tensorProduct B₀).1
    (e.exists_rep_and_eventually_zero_tensorProduct C₀).2
    (fun j ↦ (1 : T j) ⊗ₜ[S] x) ((1 : R) ⊗ₜ[S] x)
  · intro j
    -- Expose the first tensor factor to apply map_one to the inclusion.
    change incl j 1 ⊗ₜ[S] x = (1 : R) ⊗ₜ[S] x
    rw [map_one]
  · intro i j h
    -- Expose the first tensor factor to apply map_one to the transition.
    change trans i j h 1 ⊗ₜ[S] x = (1 : T j) ⊗ₜ[S] x
    rw [map_one]
  · exact hi

end AlgEquiv
