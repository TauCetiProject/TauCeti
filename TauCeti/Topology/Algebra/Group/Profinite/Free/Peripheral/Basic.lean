/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.ContinuousAut.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.Free.Abelianization

/-!
# Peripheral systems of free pro-`p` groups

Let `F` be a group with a marked topological isomorphism `e : F ≃ₜ* freeProP p (Fin r)` to the
free pro-`p` group of rank `r`. The *basis* `x_0, …, x_{r-1}` of `F` is the image of the canonical
generators under `e.symm`, and the *cusp* is `z := (x_0 ⋯ x_{r-1})⁻¹`, the inverse of the ordered
product of the basis, so that `x_0 ⋯ x_{r-1} · z = 1`. The `r + 1` elements `x_0, …, x_{r-1}, z`
form the *peripheral tuple*; for `r = 2` their conjugacy classes are the classes of the loops
around `0`, `1` and `∞` in the pro-`p` fundamental group of the thrice-punctured line.

A continuous automorphism `φ` of a pro-`p` group is *peripheral of exponent* `u ∈ ℤ_pˣ` for a
family `x` when it carries every element `y` of the peripheral tuple of `x` to a conjugate of the
`p`-adic power `y ^ u`. The predicate is stated with `IsConj` rather than with named conjugators,
so that it is a property of `φ` alone.

Inner automorphisms are peripheral of exponent one, and for the basis of a free pro-`p` group of
positive rank the exponent of a peripheral automorphism is determined by the automorphism: it is
the scalar by which `φ` acts on the class of `x_0` in the abelianization `ℤ_p ^ r`.

## Main definitions

* `TauCeti.Peripheral.basis`: the basis `i ↦ e.symm (freeProP.of i)` transported along a marked
  isomorphism `e` to the standard free pro-`p` group.
* `TauCeti.Peripheral.cusp`: the inverse `((List.ofFn x).prod)⁻¹` of the ordered product of a
  family `x`.
* `TauCeti.Peripheral.peripheralTuple`: the family `x_0, …, x_{r-1}, cusp x` indexed by
  `Fin (r + 1)`.
* `TauCeti.Peripheral.IsPeripheralAut`: a continuous automorphism carries each element of the
  peripheral tuple to a conjugate of its `p`-adic power by a unit `u`.

## Main results

* `TauCeti.Peripheral.topologicalClosure_closure_range_basis`: the basis generates `F`
  topologically.
* `TauCeti.Peripheral.hom_ext_basis`: continuous homomorphisms out of `F` into a Hausdorff monoid
  that agree on the basis are equal.
* `TauCeti.Peripheral.prod_mul_cusp`, `TauCeti.Peripheral.prod_ofFn_peripheralTuple`: the
  defining relation `x_0 ⋯ x_{r-1} · cusp x = 1`, and the ordered product of the peripheral tuple
  is `1`.
* `TauCeti.Peripheral.isPeripheralAut_conj`: inner automorphisms are peripheral of exponent one.
* `TauCeti.Peripheral.IsPeripheralAut.exponent_unique`: in positive rank, the exponent of a
  peripheral automorphism with respect to the basis is unique.

## References

* Y. Ihara, "Braids, Galois groups, and some arithmetic functions", Proc. ICM Kyoto 1990,
  99–120, for peripheral automorphisms `x ↦ x ^ λ`, `y ↦ f⁻¹ y ^ λ f` of free pro-`p` groups of
  rank two and the role of the third conjugacy class.
-/

public section

namespace TauCeti

namespace Peripheral

open Multiplicative

section Basis

variable {p r : ℕ} {F : Type*} [Group F] [TopologicalSpace F]

/-- The basis of `F` transported from the standard free pro-`p` group along a marked isomorphism
`e`: the preimages `e.symm (freeProP.of i)` of the canonical generators. -/
noncomputable def basis (e : F ≃ₜ* freeProP p (Fin r)) : Fin r → F :=
  fun i ↦ e.symm (freeProP.of i)

theorem basis_apply (e : F ≃ₜ* freeProP p (Fin r)) (i : Fin r) :
    basis e i = e.symm (freeProP.of i) :=
  (rfl)

@[simp]
theorem map_basis (e : F ≃ₜ* freeProP p (Fin r)) (i : Fin r) :
    e (basis e i) = freeProP.of i := by
  simp [basis_apply]

/-- The basis generates `F` topologically. -/
theorem topologicalClosure_closure_range_basis [IsTopologicalGroup F]
    (e : F ≃ₜ* freeProP p (Fin r)) :
    (Subgroup.closure (Set.range (basis e))).topologicalClosure = ⊤ := by
  have h := topologicalClosure_closure_image_eq_top
    (freeProP.topologicalClosure_closure_range_of_eq_top p (Fin r))
    (f := e.symm.toMulEquiv.toMonoidHom) e.symm.continuous e.symm.surjective.denseRange
  rwa [← Set.range_comp] at h

/-- Two continuous homomorphisms out of `F` into a Hausdorff monoid that agree on the basis are
equal. -/
theorem hom_ext_basis [IsTopologicalGroup F] {M : Type*} [Monoid M] [TopologicalSpace M]
    [T2Space M] (e : F ≃ₜ* freeProP p (Fin r)) {f g : F →ₜ* M}
    (h : ∀ i, f (basis e i) = g (basis e i)) : f = g :=
  ContinuousMonoidHom.toMonoidHom_injective <|
    MonoidHom.eq_of_eqOn_of_topologicalClosure_closure_eq_top
      (topologicalClosure_closure_range_basis e) f.continuous g.continuous
      (Set.forall_mem_range.mpr h)

end Basis

section Cusp

variable {G H : Type*} [Group G] [Group H] {r : ℕ}

/-- The cusp of a family `x : Fin r → G`: the inverse `(x_0 ⋯ x_{r-1})⁻¹` of the product of the
family in order. The product is a `List.prod`, since `G` need not be commutative. -/
def cusp (x : Fin r → G) : G :=
  ((List.ofFn x).prod)⁻¹

theorem cusp_def (x : Fin r → G) : cusp x = ((List.ofFn x).prod)⁻¹ :=
  (rfl)

@[simp]
theorem inv_cusp (x : Fin r → G) : (cusp x)⁻¹ = (List.ofFn x).prod :=
  inv_inv _

/-- The defining relation of the cusp: `x_0 ⋯ x_{r-1} · cusp x = 1`. -/
@[simp]
theorem prod_mul_cusp (x : Fin r → G) : (List.ofFn x).prod * cusp x = 1 :=
  mul_inv_cancel _

/-- Homomorphisms carry the cusp of a family to the cusp of its image. -/
@[simp]
theorem map_cusp {M : Type*} [FunLike M G H] [MonoidHomClass M G H] (f : M) (x : Fin r → G) :
    f (cusp x) = cusp (f ∘ x) := by
  rw [cusp_def, cusp_def, map_inv, map_list_prod, List.map_ofFn]

/-- The peripheral tuple of a family `x : Fin r → G`: the family `x_0, …, x_{r-1}, cusp x`,
indexed by `Fin (r + 1)`. -/
def peripheralTuple (x : Fin r → G) : Fin (r + 1) → G :=
  Fin.snoc x (cusp x)

@[simp]
theorem peripheralTuple_castSucc (x : Fin r → G) (i : Fin r) :
    peripheralTuple x i.castSucc = x i :=
  Fin.snoc_castSucc ..

@[simp]
theorem peripheralTuple_last (x : Fin r → G) : peripheralTuple x (Fin.last r) = cusp x :=
  Fin.snoc_last ..

/-- The ordered product of the peripheral tuple is `1`. -/
theorem prod_ofFn_peripheralTuple (x : Fin r → G) : (List.ofFn (peripheralTuple x)).prod = 1 := by
  rw [List.ofFn_succ', List.prod_concat]
  simp

/-- Homomorphisms carry the peripheral tuple of a family to the peripheral tuple of its image. -/
@[simp]
theorem map_peripheralTuple {M : Type*} [FunLike M G H] [MonoidHomClass M G H] (f : M)
    (x : Fin r → G) (i : Fin (r + 1)) : f (peripheralTuple x i) = peripheralTuple (f ∘ x) i := by
  induction i using Fin.lastCases with
  | last => simp
  | cast i => simp

end Cusp

section IsPeripheralAut

variable {p r : ℕ} [Fact p.Prime] {F : Type*} [Group F] [TopologicalSpace F]
  [IsTopologicalGroup F] [CompactSpace F] [TotallyDisconnectedSpace F]

/-- A continuous automorphism `φ` of a pro-`p` group is **peripheral of exponent `u`** for a family
`x` when it carries every element `y` of the peripheral tuple `x_0, …, x_{r-1}, cusp x` to a
conjugate of the `p`-adic power `y ^ u`. -/
def IsPeripheralAut (hF : IsProP p F) (x : Fin r → F) (u : ℤ_[p]ˣ) (φ : ContinuousAut F) :
    Prop :=
  ∀ i : Fin (r + 1), IsConj (hF.padicPow (peripheralTuple x i) u) (φ (peripheralTuple x i))

/-- An automorphism is peripheral of exponent `u` exactly when it carries each `x_i` and the cusp
to conjugates of their `u`-th powers. -/
@[simp]
theorem isPeripheralAut_iff (hF : IsProP p F) (x : Fin r → F) (u : ℤ_[p]ˣ)
    (φ : ContinuousAut F) :
    IsPeripheralAut hF x u φ ↔
      (∀ i, IsConj (hF.padicPow (x i) u) (φ (x i))) ∧
        IsConj (hF.padicPow (cusp x) u) (φ (cusp x)) := by
  rw [IsPeripheralAut, Fin.forall_fin_succ']
  simp only [peripheralTuple_castSucc, peripheralTuple_last]

/-- **Inner automorphisms are peripheral of exponent one.** -/
theorem isPeripheralAut_conj (hF : IsProP p F) (x : Fin r → F) (g : F) :
    IsPeripheralAut hF x 1 (ContinuousAut.conj g) := fun i ↦
  isConj_iff.mpr ⟨g, by rw [ContinuousAut.conj_apply]; simp⟩

/-- **The identity is peripheral of exponent one.** -/
theorem isPeripheralAut_one (hF : IsProP p F) (x : Fin r → F) :
    IsPeripheralAut hF x 1 (1 : ContinuousAut F) := by
  simpa using isPeripheralAut_conj hF x 1

/-- **The exponent of a peripheral automorphism is determined.** For a free pro-`p` group of
positive rank with its basis, an automorphism peripheral of exponents `u` and `v` has `u = v`. The
exponent is the scalar by which the automorphism acts on the class of `x_0` in the abelianization
`ℤ_p ^ r`. -/
theorem IsPeripheralAut.exponent_unique {hF : IsProP p F} {e : F ≃ₜ* freeProP p (Fin r)}
    (hr : 0 < r) {u v : ℤ_[p]ˣ} {φ : ContinuousAut F} (hu : IsPeripheralAut hF (basis e) u φ)
    (hv : IsPeripheralAut hF (basis e) v φ) : u = v := by
  let i₀ : Fin r := ⟨0, hr⟩
  -- the `u`-th and `v`-th powers of `x_0` are conjugate, both being conjugate to `φ x_0`
  have hc : IsConj (hF.padicPow (basis e i₀) u) (hF.padicPow (basis e i₀) v) := by
    have h₁ := hu i₀.castSucc
    have h₂ := hv i₀.castSucc
    rw [peripheralTuple_castSucc] at h₁ h₂
    exact h₁.trans h₂.symm
  -- read off exponent sums, which live in the abelian group `ℤ_p ^ r`
  let f : F →ₜ* Multiplicative (Fin r → ℤ_[p]) :=
    (freeProP.exponentSum p (Fin r)).comp (e : F →ₜ* freeProP p (Fin r))
  have hf : ∀ l : ℤ_[p], f (hF.padicPow (basis e i₀) l) = ofAdd (l • Pi.single i₀ 1) := by
    intro l
    refine (IsProP.map_padicPow hF (isProP_multiplicative_pi_padicInt p (Fin r)) f.toMonoidHom
      f.continuous _ l).trans ?_
    simp [f, freeProP.exponentSum_of]
  have h := congr_fun (ofAdd.injective ((hf u).symm.trans
    ((isConj_iff_eq.mp (f.toMonoidHom.map_isConj hc)).trans (hf v)))) i₀
  simpa [Units.ext_iff] using h

end IsPeripheralAut

end Peripheral

end TauCeti
